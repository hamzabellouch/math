import Mathlib
import OAI.Combinatorics.RamseyFive.Iteration.StageState

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
variable {A : Type*} [Fintype A] {B : A→Type*} [∀a,Fintype (B a)]
lemma sigmaLaw_positive (p : Law A) (q : ∀a,Law (B a)) (z : Sigma B)
    (hz : 0<sigmaLaw p q z) : 0<p z.1 ∧ 0<q z.1 z.2 := by
  change 0<p z.1*q z.1 z.2 at hz
  exact (mul_pos_iff.mp hz).resolve_right (fun h=>(p.nonneg _).not_gt h.1)
lemma map_sigma_first (p : Law A) (q : ∀a,Law (B a)) :
    map (sigmaLaw p q) Sigma.fst=p := by
  apply Law.ext_mean
  intro f
  rw [mean_map,mean_sigma]
  simp only [mean_const]
lemma sigma_stream {Γ : Type*} [Fintype Γ] (p : Law A) (q : ∀a,Law (B a)) (s : A→Γ) :
    map (sigmaLaw p q) (fun z=>s z.1)=map p s := by
  change map (sigmaLaw p q) (s ∘ Sigma.fst)=map p s
  rw [←map_comp,map_sigma_first]
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.SelectedTuple.SelectedStream
open FiniteEntropy
open scoped Classical
variable {Ω β α : Type*} [Fintype Ω] [Fintype β] [Fintype α]
  {Γ : Ω→Type*} [∀a,Fintype (Γ a)] {N n : ℕ} {admissible : (Fin N→α)→Prop}

def augmentSigma (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible) (q : ∀a,Law (Γ a)) :
    SelectedStream (Ω:=Sigma Γ) (β:=β) N n admissible where
  law:=sigmaLaw S.law q
  stream:=fun z=>S.stream z.1
  tuple:=fun z=>S.tuple z.1
  reverse:=S.reverse
  view:=S.view
  selected:=fun z hz=>S.selected z.1 (sigmaLaw_positive S.law q z hz).1
  good:=fun z hz=>S.good z.1 (sigmaLaw_positive S.law q z hz).1
  density:=S.density
  density_nonneg:=S.density_nonneg
  density_bound:=by intro s;rw [sigma_stream];exact S.density_bound s
end SharpRamseyFive.SelectedTuple.SelectedStream

end

end OAI
