import OAI.NumberTheory.DirichletL.Descent.CanonicalRankExistenceSuccessor
import OAI.NumberTheory.DirichletL.Descent.CanonicalRankDepthParameters
import OAI.NumberTheory.DirichletL.Descent.CanonicalEnergyExistenceData

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open CanonicalCubeSeparation

def RankReferenceCutoffs:Prop :=
  ∀lo hi:ℝ,0<lo→0≤hi→∃(Vlog:𝓢(ℝ,ℂ))(Alog:ℝ),
    (∀x,Vlog x≠0→|x|≤Alog) ∧
    (∀x,|x|≤columnWindowRadius lo hi→Vlog x=1)

def RankReferenceThresholds:Prop :=
  ∀eta:ℝ,0<eta→∀hi Alog window:ℝ,∃Zt:ℝ,1<Zt ∧ ∀Z:ℝ,Zt≤Z→
    2≤Z ∧ 2≤Z^eta ∧ Real.exp 1≤Z^eta ∧ 1≤eta*Real.log Z ∧
    hi≤Z^eta ∧ Real.exp Alog≤Z^eta ∧ Real.exp window≤Z^eta

theorem rank_energy_exists_all_of_references
    (href:RankReferenceCutoffs)(hthreshold:RankReferenceThresholds)
    (L cstar cutoff eta:ℝ)(K:ℕ)
    (hL:1≤L)(hcstar:0<cstar)(hcut:0<cutoff)(hcutL:cutoff≤L)
    (hcutc:cutoff≤cstar/200)(heta:0<eta)(heta1:eta≤1)
    (hetac:eta≤cstar/100000)(hetad:eta≤cutoff/32):
    ∀n:ℕ,∀(W:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo→0≤hi→
      Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi→RankEnergyExists n L cstar cutoff eta K W :=by
  intro n
  induction n with
  | zero =>
      intro W lo hi hlo hhi hsW
      exact rank_energy_exists_zero L cstar cutoff eta hcut K W
  | succ n ih =>
      intro W lo hi hlo hhi hsW
      obtain ⟨Vlog,Alog,hbox,hone⟩:=href lo hi hlo hhi
      exact rank_energy_exists_succ_of_reference n L cstar cutoff eta K hL hcstar hcut hcutL
        hcutc heta heta1 hetac hetad ih W lo hi hlo hhi hsW Vlog Alog hbox hone
        (fun window=>hthreshold eta heta hi Alog window)

theorem canonical_energy_exists_of_references
    (href:RankReferenceCutoffs)(hthreshold:RankReferenceThresholds)
    (Mcap Fcap c eps:ℝ)(hM:0≤Mcap)(hF:0≤Fcap)(hc:0<c)(heps:0<eps)
    (K:ℕ)(W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi):
    CanonicalEnergyExists Mcap Fcap c eps (Fcap+1) K W :=by
  obtain ⟨n,cutoff,eta,hn,hpos,hcut,heta,heta1,hetad,hcutL,hcutc,hetac,hrow,hcap,hmargin0,hmargin,hloss0,hloss⟩:=
    actual_rank_top_parameters Mcap Fcap c eps hM hF hc heps
  have he:=rank_energy_exists_all_of_references href hthreshold (Fcap+1) c cutoff eta K
    (by linarith) hc hcut hcutL hcutc heta heta1 hetac hetad n W lo hi hlo hhi hsW
  exact canonical_energy_of_rank n (Fcap+1) c cutoff eta Mcap Fcap c eps K W
    hrow hcap hmargin hloss.le he

end SevenEighths.InverseMoment

end

end OAI
