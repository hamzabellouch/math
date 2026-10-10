import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarOneAtomMoments
import OAI.Probability.SKBarriers.Coverage.ThermodynamicLimit

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

def oneAtomTrial (β v : ℝ) : ℝ := scalarGaussianValue v+(β^2/4)*(1-v^2/β^2)^2

theorem oneAtomTrial_hasDerivAt {β : ℝ} (hβ : 0 < β) (v : ℝ) :
    HasDerivAt (oneAtomTrial β) (v*(v^2/β^2-scalarGaussianOverlap v)) v := by
  have H := (scalarGaussianValue_derivative v).add
    ((((hasDerivAt_const v (1:ℝ)).sub (((hasDerivAt_id v).pow 2).div_const (β^2))).pow 2).const_mul (β^2/4))
  apply H.congr_deriv
  dsimp only [Pi.sub_apply,Pi.pow_apply,id_eq]
  norm_num only [Nat.cast_ofNat,show 2-1=1 by rfl,pow_one]
  field_simp [hβ.ne']
  ring

theorem oneAtomTrial_zero (β : ℝ) : oneAtomTrial β 0 = Real.log 2+β^2/4 := by
  simp [oneAtomTrial,scalarGaussianValue,scalarSpinTerminal]

theorem exists_oneAtomTrial_lt_annealed {β : ℝ} (hβ : 1 < β) :
    ∃ v : ℝ, 0 < v ∧ v < β ∧ oneAtomTrial β v < Real.log 2+β^2/4 := by
  have hβpos : 0 < β := lt_trans zero_lt_one hβ
  have hc : 1/β^2 < (1:ℝ) := (div_lt_one (sq_pos_of_pos hβpos)).mpr (by nlinarith)
  have HE := scalarGaussianOverlap_normalized_tendsto.eventually (eventually_gt_nhds hc)
  have Hβ : ∀ᶠ v : ℝ in 𝓝[>] 0, v < β :=
    (eventually_lt_nhds hβpos).filter_mono nhdsWithin_le_nhds
  obtain ⟨b,hb,hE⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (HE.and Hβ)
  have hbpos : 0 < b := hb
  have hanti : StrictAntiOn (oneAtomTrial β) (Set.Icc 0 b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      ((continuous_iff_continuousAt.mpr (fun v => (oneAtomTrial_hasDerivAt hβpos v).continuousAt)).continuousOn)
    intro v hv
    rw [interior_Icc] at hv
    rw [(oneAtomTrial_hasDerivAt hβpos v).deriv]
    apply mul_neg_of_pos_of_neg hv.1
    have H := (hE ⟨hv.1,hv.2.le⟩).1
    have H' := (lt_div_iff₀ (sq_pos_of_pos hv.1)).mp H
    rw [div_eq_mul_inv] at H' ⊢
    exact sub_neg.mpr (by nlinarith)
  refine ⟨b,hbpos,(hE ⟨hbpos,le_rfl⟩).2,?_⟩
  rw [← oneAtomTrial_zero β]
  exact hanti ⟨le_rfl,hbpos.le⟩ ⟨hbpos.le,le_rfl⟩ hbpos

theorem extendedQuantileParisi_one (β q : ℝ) :
    extendedQuantileParisi 0 β (fun _ => q) =
      scalarGaussianValue (β*Real.sqrt q)+(β^2/4)*(1-q)^2 := by
  simp only [extendedQuantileParisi,scalarHierarchy]
  have he : (Fin.last 0 : Fin 1) = 0 := rfl
  rw [he,cumulativeGapMap_zero]
  norm_num only [quantileMass,Fin.val_zero,Nat.cast_add,Nat.cast_zero,Nat.cast_one,zero_add,zero_div]
  simp only [scalarStep,gaussianStep,ite_true,zero_add,one_mul,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,one_smul]
  change scalarGaussianValue (β*Real.sqrt q)+(β^2/4)*(1-2*q+q^2) = _
  ring

theorem oneAtomTrial_eq_extended {β v : ℝ} (hβ : 0 < β) (hv : 0 ≤ v) :
    oneAtomTrial β v = extendedQuantileParisi 0 β (fun _ => v^2/β^2) := by
  rw [extendedQuantileParisi_one]
  have hs : β*Real.sqrt (v^2/β^2) = v := by
    rw [Real.sqrt_div (sq_nonneg v),Real.sqrt_sq hv,Real.sqrt_sq hβ.le]
    field_simp [hβ.ne']
  rw [hs]
  rfl

theorem finiteParisiInf_lt_annealed {β : ℝ} (hβ : 1 < β) :
    finiteParisiInf β < Real.log 2+β^2/4 := by
  obtain ⟨v,hv,hvβ,H⟩ := exists_oneAtomTrial_lt_annealed hβ
  have hβpos : 0 < β := lt_trans zero_lt_one hβ
  rw [oneAtomTrial_eq_extended hβpos hv.le] at H
  apply lt_of_le_of_lt (finiteParisiInf_le β (fun _ => v^2/β^2) monotone_const (fun _ => ?_)) H
  constructor
  · positivity
  · apply (div_le_one (sq_pos_of_pos hβpos)).mpr
    nlinarith
end SK.Analytic

end
end

end

end OAI
