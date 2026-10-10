import OAI.Analysis.AllenCahn.ConeDerivatives
import OAI.Analysis.AllenCahn.CompactCone

namespace OAI

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
open DeGiorgiCompactness (JetSpace CoherentJets pdeJetCone)

def smoothJet {n : ℕ} (f : Space n → ℝ) (hf : ContDiff ℝ ∞ f) : JetSpace n :=
  fun l => ⟨coordinateJet f l, (coordinateJet_smooth hf l).continuous⟩

lemma smoothJet_coherent {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) :
    CoherentJets (smoothJet f hf) := by
  intro l
  exact ⟨(coordinateJet_smooth hf l).differentiable (by simp), fun _ _ => rfl⟩

lemma smoothJet_mem {n : ℕ} {P f : Space n → ℝ} (hf : f ∈ positiveLinearCone P) :
    smoothJet f hf.1 ∈ pdeJetCone P := by
  refine ⟨smoothJet_coherent hf.1, hf.2.1, ?_, hf.2.2.2⟩
  intro x
  change (∑ i : Fin n, coordDeriv (coordDeriv f i) i x) = P x*f x
  rw [← laplacian_eq_sum_coordDeriv (smooth_C2 hf.1)]
  exact hf.2.2.1 x

lemma jetCone_base_mem {n : ℕ} {P : Space n → ℝ} {g : JetSpace n}
    (hg : g ∈ pdeJetCone P) : (g [] : Space n → ℝ) ∈ positiveLinearCone P := by
  have hs := DeGiorgiCompactness.coherentJets_smooth hg.1 []
  refine ⟨hs, hg.2.1, ?_, hg.2.2.2⟩
  intro x
  rw [laplacian_eq_sum_coordDeriv (smooth_C2 hs), ← hg.2.2.1 x]
  apply Finset.sum_congr rfl
  intro i hi
  have he : coordDeriv (g [] : Space n → ℝ) i = (g [i] : Space n → ℝ) :=
    funext ((hg.1 []).2 i)
  rw [he]
  exact (hg.1 [i]).2 i x

lemma coherentJets_eq_smoothJet {n : ℕ} {g : JetSpace n} (hg : CoherentJets g) :
    g = smoothJet (g [] : Space n → ℝ) (DeGiorgiCompactness.coherentJets_smooth hg []) :=
  DeGiorgiCompactness.coherentJets_eq_of_base hg (smoothJet_coherent _) rfl

lemma jetCone_jet_eq {n : ℕ} {g : JetSpace n} (hg : CoherentJets g)
    (l : List (Fin n)) (x : Space n) : g l x = coordinateJet (g [] : Space n → ℝ) l x := by
  conv_lhs => rw [coherentJets_eq_smoothJet hg]
  rfl

lemma conePotential_harnack_base {n : ℕ} {ν : Space n} (hν : ‖ν‖=1)
    {f : Space n → ℝ} (hf : f ∈ positiveLinearCone (conePotential ν)) (x : Space n) :
    f x ≤ Real.exp (Real.sqrt (linearLogGradientBound n 2)*‖x‖) := by
  have H := positive_linear_harnack hf.1 (conePotential_smooth ν)
    (positiveLinearCone_pos (fun y => (conePotential_bounds ν y).2) hf) (by norm_num : (0:ℝ)≤2)
    (fun y => by rw [abs_of_nonneg (by linarith [(conePotential_bounds ν y).1] : 0≤conePotential ν y)]; exact (conePotential_bounds ν y).2)
    (conePotential_coord_bound hν) hf.2.2.1 0 x
  simpa only [hf.2.2.2, mul_one, sub_zero] using H

lemma conePotential_jetCone_compact {n : ℕ} {ν : Space n} (hν : ‖ν‖=1) :
    IsCompact (pdeJetCone (conePotential ν)) := by
  apply DeGiorgiCompactness.pdeJetCone_compact_of_local_bounds
  intro l R hR
  obtain ⟨M,hM,hMb⟩ := conePotential_relative_jets hν l
  choose N hN hNb using fun i : Fin n => conePotential_relative_jets hν (i::l)
  let B := Real.exp (Real.sqrt (linearLogGradientBound n 2)*R)
  have hB : 0 ≤ B := (Real.exp_pos _).le
  have hsum : 0 ≤ ∑ i, N i := Finset.sum_nonneg (fun i _ => hN i)
  let L := (M+‖DeGiorgiCompactness.coordinateDual n‖*(∑ i, N i))*B
  have hnorm : 0 ≤ ‖DeGiorgiCompactness.coordinateDual n‖ := by positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨⟨L,hL⟩, ?_⟩
  intro g hg x hx
  have hf := jetCone_base_mem hg
  have hb : g [] x ≤ B := (conePotential_harnack_base hν hf x).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg _)))
  have hval : |g l x| ≤ M*B := by
    rw [jetCone_jet_eq hg.1]
    exact (hMb _ hf x).trans (mul_le_mul_of_nonneg_left hb hM)
  have hder : ‖fderiv ℝ (g l : Space n → ℝ) x‖ ≤
      ‖DeGiorgiCompactness.coordinateDual n‖*(∑ i, N i)*B := by
    calc ‖fderiv ℝ (g l : Space n → ℝ) x‖ ≤
        ‖DeGiorgiCompactness.coordinateDual n‖*((∑ i, N i)*B) := by
          apply DeGiorgiCompactness.fderiv_norm_le_coord_bound _ _ (by positivity)
          intro i
          rw [(hg.1 l).2, jetCone_jet_eq hg.1]
          exact (hNb i _ hf x).trans ((mul_le_mul_of_nonneg_left hb (hN i)).trans
            (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun j _ => hN j) (Finset.mem_univ i)) hB))
      _ = _ := by ring
  change |g l x| ≤ L ∧ ‖fderiv ℝ (g l : Space n → ℝ) x‖ ≤ L
  constructor
  · exact hval.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hnorm hsum)) hB)
  · exact hder.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hM) hB)

end DeGiorgi
end

end OAI
