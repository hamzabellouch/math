import Mathlib
import OAI.Probability.BinarySweep.Mixing.DimensionSeries

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Young

lemma decay_eighth {D : ℝ} (hD : 0<D) :
    D*(D*(D^(-5:ℝ))^2)=(D^8)⁻¹ := by
  rw [Real.rpow_neg hD.le,show D^(5:ℝ)=D^5 from Real.rpow_natCast D 5]
  field_simp

lemma centered_power_moment {d w : ℕ} {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Slot d)) V) [ρ.IsIrreducible]
    (hD : 1<Module.finrank ℂ V) {g : ℝ} (hgw : 5≤g*(w:ℝ))
    (hA : ‖complexAverage ρ (fun g => (binaryLaw d g:ℂ))‖≤(Module.finrank ℂ V:ℝ)^(-g)) :
    (Module.finrank ℂ V:ℝ)*evenMoment 1
      (groupAverage ρ (fun g => (sweepLaw d w g-uniformLaw _ g:ℂ))) ≤
        ((Module.finrank ℂ V:ℝ)^8)⁻¹ := by
  obtain ⟨v,hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0<Module.finrank ℂ V from by omega)
  have : Nontrivial V := ⟨⟨v,0,hv⟩⟩
  let D : ℝ := Module.finrank ℂ V
  have hp : 0<D := by dsimp [D]; exact_mod_cast (by omega : 0<Module.finrank ℂ V)
  have hone : 1≤D := by dsimp [D]; exact_mod_cast hD.le
  have he : complexAverage ρ (fun g => (sweepLaw d w g-uniformLaw _ g:ℂ))=
      (complexAverage ρ (fun g => (binaryLaw d g:ℂ)))^w := by
    simp only [complexAverage_sub,complexAverage_uniform_zero ρ hD,
      sub_zero,sweepLaw,complexAverage_power]
  have hb : ‖complexAverage ρ (fun g => (sweepLaw d w g-uniformLaw _ g:ℂ))‖≤D^(-5:ℝ) := by
    rw [he]
    calc
      _ ≤ ‖complexAverage ρ (fun g => (binaryLaw d g:ℂ))‖^w := norm_pow_le _ _
      _ ≤ (D^(-g))^w := pow_le_pow_left₀ (norm_nonneg _) hA w
      _ = D^((-g)*(w:ℝ)) := (Real.rpow_mul_natCast hp.le _ _).symm
      _ ≤ D^(-5:ℝ) := Real.rpow_le_rpow_of_exponent_le hone (by nlinarith)
  have hm := evenMoment_one_norm_bound
    (complexAverage ρ (fun g => (sweepLaw d w g-uniformLaw _ g:ℂ)))
    (Real.rpow_nonneg hp.le _) hb
  change evenMoment 1 (groupAverage ρ _)≤D*(D^(-5:ℝ))^2 at hm
  exact (mul_le_mul_of_nonneg_left hm hp.le).trans_eq (decay_eighth hp)

def binarySlotsFin (d : ℕ) : Slot d ≃ Fin (2^d) :=
  Fintype.equivOfCardEq (by simp [Slot])

lemma partition_slot_flat {d : ℕ} (p : (2^d).Partition) (w : ℕ)
    (hd : 0<d) (hw : 0<w) (hp : flatTail (diagram p)=0) :
    evenMoment 1 (groupAverage
      ((partitionHilbertRep p).comp (binarySlotsFin d).permCongrHom.toMonoidHom)
      (fun g => (sweepLaw d w g-uniformLaw _ g:ℂ)))=0 := by
  have he : (partitionHilbertRep p).comp (binarySlotsFin d).permCongrHom.toMonoidHom=
      (hilbertSpecht (diagram p)).comp
        ((cellsEquivFin p).trans (binarySlotsFin d).symm).symm.permCongrHom.toMonoidHom := by
    rfl
  rw [he]
  exact flat_shape_moment_zero _ _ _ hp (sweep_centered_mass d w) (sweep_centered_sign hd hw)

theorem binary_variation_bound_exists : ∃ w : ℕ, 0<w ∧ ∃ d₀ : ℕ,
    ∀ d ≥ d₀, totalVariation (sweepLaw d w) (uniformLaw (Equiv.Perm (Slot d)))^2 ≤
      (1/4:ℝ)*dimensionSeries (2^d) := by
  obtain ⟨g,hg,d₀,hcont⟩ := binary_hilbert_contraction
  obtain ⟨w,hw⟩ := exists_nat_gt (5/g)
  have hwpos : 0<w := by
    have hh : (0:ℝ)<(w:ℝ) := (div_pos (by norm_num) hg).trans hw
    exact_mod_cast hh
  have hgw : 5≤g*(w:ℝ) := by
    have hh := (div_lt_iff₀ hg).mp hw
    nlinarith
  refine ⟨w,hwpos,max d₀ 1,?_⟩
  intro d hd
  have hd₀ : d₀≤d := (le_max_left _ _).trans hd
  have hdpos : 0<d := by have := (le_max_right d₀ 1).trans hd; omega
  refine (variation_fourier_equiv (binarySlotsFin d) _ _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  unfold dimensionSeries
  apply Finset.sum_le_sum
  intro p _
  by_cases hp : flatTail (diagram p)=0
  · rw [ite_eq_left hp,partition_slot_flat p w hdpos hwpos hp,mul_zero]
  · rw [ite_eq_right hp]
    let ρ : Representation ℂ (Equiv.Perm (Slot d)) (PartitionHilbert p) :=
      (partitionHilbertRep p).comp (binarySlotsFin d).permCongrHom.toMonoidHom
    have : ρ.IsIrreducible := irreducible_comp_equiv _ _
    exact centered_power_moment ρ (partition_dimension_gt_one p (by omega)) hgw
      (hcont d hd₀ _ ρ inferInstance (fun g v => partitionHilbertRep_unitary p _ v))

end BinaryCoordinateSweeps

end

namespace BinaryCoordinateSweeps

def BinaryMainTarget : Prop := BinaryContractionTarget ∧
    (∀ d : ℕ, 0 < d → ∑ g : Equiv.Perm (Slot d),
      binaryLaw d g * realSign g = 0) ∧ UniformSweepMixingTarget
end BinaryCoordinateSweeps

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Young

lemma binary_dimension_series_tendsto : Filter.Tendsto (fun d : ℕ => dimensionSeries (2^d))
    Filter.atTop (nhds 0) := by
  apply dimensionSeries_tendsto.comp
  apply Filter.tendsto_atTop.2
  intro b
  exact Filter.eventually_atTop.2 ⟨b,fun d hd => hd.trans (Nat.le_of_lt d.lt_two_pow_self)⟩

theorem constant_sweep_mixing : ConstantSweepMixingTarget := by
  obtain ⟨w,hw,d₀,hbound⟩ := binary_variation_bound_exists
  refine ⟨w,?_⟩
  intro ε hε
  have heps : 0<4*ε^2 := by positivity
  have ht : ∀ᶠ d : ℕ in Filter.atTop, dimensionSeries (2^d)<4*ε^2 :=
    (Filter.Tendsto.eventually_lt_const heps binary_dimension_series_tendsto)
  obtain ⟨d₁,hd₁⟩ := Filter.eventually_atTop.1 ht
  refine ⟨max d₀ d₁,?_⟩
  intro d hd τ
  rw [totalVariation_fromInitial]
  have hb := hbound d ((le_max_left _ _).trans hd)
  have hs := hd₁ d ((le_max_right _ _).trans hd)
  have hh : totalVariation (sweepLaw d w) (uniformLaw (Equiv.Perm (Slot d)))^2<ε^2 := by
    nlinarith
  nlinarith

theorem uniform_sweep_mixing : UniformSweepMixingTarget := by
  obtain ⟨w,hw⟩ := constant_sweep_mixing
  refine ⟨w,?_⟩
  intro ε hε
  obtain ⟨d₀,hd₀⟩ := hw ε hε
  exact ⟨d₀,fun d hd τ => (hd₀ d hd τ).le⟩

theorem binary_main : BinaryMainTarget :=
  ⟨binary_contraction,binary_sign_annihilated,uniform_sweep_mixing⟩

end BinaryCoordinateSweeps

end

end OAI
