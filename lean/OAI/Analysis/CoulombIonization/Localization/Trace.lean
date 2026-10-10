import Mathlib
import OAI.Analysis.CoulombIonization.Localization.Cut

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
namespace CoulombPackets

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
open scoped InnerProductSpace
variable {ι : Type*} [Countable ι]

omit [Countable ι] in
lemma basis_packet_parseval (b : HilbertBasis ι ℂ (Lp ℂ 2 (volume : Measure V)))
    (u : Lp ℂ 2 (volume : Measure V)) :
    HasSum (fun i => ‖inner ℂ u (b i)‖^2) (‖u‖^2) := by
  have hh := (b.hasSum_inner_mul_inner u u).mapL Complex.reCLM
  convert hh using 1
  · ext i
    simp only [Complex.reCLM_apply, ← inner_conj_symm (b i) u,
      Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  · simp only [Complex.reCLM_apply, inner_self_eq_norm_sq_to_K,
      ← RCLike.ofReal_pow]
    rfl

lemma selectedFrame_norm_sq_lintegral (g : 𝓢(V, ℝ))
    (s : Set (V × V)) (hs : MeasurableSet s) (u : Lp ℂ 2 (volume : Measure V)) :
    ENNReal.ofReal (‖selectedFrame g s hs u‖^2) =
      ∫⁻ p in s, ENNReal.ofReal (‖frame g u p‖^2) ∂((volume : Measure V).prod volume) := by
  change ENNReal.ofReal (‖cut s hs (frame g u)‖^2) = _
  rw [cut_norm_sq]
  exact ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp (frame g u)).aestronglyMeasurable).1
      (Lp.memLp (frame g u))).integrableOn (Filter.Eventually.of_forall fun _ => sq_nonneg _)

lemma densityMatrix_trace (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1)
    (s : Set (V × V)) (hs : MeasurableSet s)
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (volume : Measure V))) :
    ∑' i, ENNReal.ofReal (inner ℂ (densityMatrix g s hs (b i)) (b i)).re =
      ((volume : Measure V).prod volume) s := by
  have hsq (i : ι) : (inner ℂ (densityMatrix g s hs (b i)) (b i)).re =
      ‖selectedFrame g s hs (b i)‖^2 :=
    (ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left (selectedFrame g s hs) (b i)).symm
  simp_rw [hsq, selectedFrame_norm_sq_lintegral]
  have hm (i : ι) : AEMeasurable (fun p : V × V => ENNReal.ofReal (‖frame g (b i) p‖^2))
      (((volume : Measure V).prod volume).restrict s) :=
    (((Lp.memLp (frame g (b i))).aestronglyMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal).restrict
  rw [← lintegral_tsum hm]
  calc
    _ = ∫⁻ _p in s, (1 : ℝ≥0∞) ∂((volume : Measure V).prod volume) := by
      apply lintegral_congr_ae
      have hae := ae_all_iff.2 (fun i => frame_ae_packet g hg (b i))
      filter_upwards [ae_restrict_of_ae hae] with p hp
      simp_rw [hp]
      have hh := basis_packet_parseval b (packet g p)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hh.summable,
        hh.tsum_eq, packet_norm_sq, hg, ENNReal.ofReal_one]
    _ = _ := by simp

end

section
open CoulombPauli
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma packet_coefficient_measurable (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1)
    (u : Lp ℂ 2 (volume : Measure V)) :
    AEMeasurable (fun p => ENNReal.ofReal (‖inner ℂ (packet g p) u‖^2))
      ((volume : Measure V).prod volume) := by
  exact (((Lp.memLp (frame g u)).aestronglyMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal).congr
    (by simpa only [Function.comp_def, Pi.pow_apply] using
      (frame_ae_packet g hg u).fun_comp (fun c : ℂ => ENNReal.ofReal (‖c‖^2)))

lemma packet_plancherel (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1)
    (u : Lp ℂ 2 (volume : Measure V)) :
    (∫⁻ p, ENNReal.ofReal (‖inner ℂ (packet g p) u‖^2)
      ∂((volume : Measure V).prod volume)) = ENNReal.ofReal (‖u‖^2) := by
  calc
    _ = ∫⁻ p, ENNReal.ofReal (‖frame g u p‖^2) ∂((volume : Measure V).prod volume) :=
      lintegral_congr_ae ((frame_ae_packet g hg u).symm.fun_comp
        (fun c : ℂ => ENNReal.ofReal (‖c‖^2)))
    _ = ENNReal.ofReal (‖frame g u‖^2) := by
      rw [CoulombPauli.l2_norm_sq]
      exact (ofReal_integral_eq_lintegral_ofReal
        ((memLp_two_iff_integrable_sq_norm
          (Lp.memLp (frame g u)).aestronglyMeasurable).1 (Lp.memLp (frame g u)))
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
    _ = _ := by rw [frame_norm g hg]

variable {B : Type*} [MeasurableSpace B] {ν : Measure B} [SigmaFinite ν]
  [SeparableSpace (Lp ℂ 2 ν)]

def partialOccupation (g : 𝓢(V, ℝ)) (ψ : Lp ℂ 2 ((volume : Measure V).prod ν))
    (p : V × V) : ℝ := ‖(tensorLeft (ν := ν) (packet g p)).adjoint ψ‖^2

lemma partialOccupation_measurable (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1)
    (ψ : Lp ℂ 2 ((volume : Measure V).prod ν)) :
    AEMeasurable (fun p => ENNReal.ofReal (partialOccupation g ψ p))
      ((volume : Measure V).prod volume) := by
  obtain ⟨w,b,-⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 ν)
  let : Countable w := hilbertBasis_countable b
  have hm (j : w) := packet_coefficient_measurable g hg ((tensorRight (b j)).adjoint ψ)
  have he (p : V × V) : ENNReal.ofReal (partialOccupation g ψ p) =
      ∑' j, ENNReal.ofReal (‖inner ℂ (packet g p) ((tensorRight (b j)).adjoint ψ)‖^2) := by
    have h := basis_parseval b ((tensorLeft (ν := ν) (packet g p)).adjoint ψ)
    rw [partialOccupation, ← h.tsum_eq,
      ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) h.summable]
    simp_rw [tensor_adjoint_exchange]
  simp_rw [he]
  exact AEMeasurable.tsum hm

lemma partialOccupation_mass (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1)
    (ψ : Lp ℂ 2 ((volume : Measure V).prod ν)) :
    (∫⁻ p, ENNReal.ofReal (partialOccupation g ψ p)
      ∂((volume : Measure V).prod volume)) = ENNReal.ofReal (‖ψ‖^2) := by
  obtain ⟨w,b,-⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 ν)
  obtain ⟨v,a,-⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 (volume : Measure V))
  let : Countable w := hilbertBasis_countable b
  calc
    _ = ∫⁻ p, ∑' j, ENNReal.ofReal
        (‖inner ℂ (packet g p) ((tensorRight (b j)).adjoint ψ)‖^2)
        ∂((volume : Measure V).prod volume) := by
      apply lintegral_congr
      intro p
      have h := basis_parseval b ((tensorLeft (ν := ν) (packet g p)).adjoint ψ)
      rw [partialOccupation, ← h.tsum_eq,
        ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) h.summable]
      simp_rw [tensor_adjoint_exchange]
    _ = ∑' j, ENNReal.ofReal (‖(tensorRight (b j)).adjoint ψ‖^2) := by
      rw [lintegral_tsum (fun j => packet_coefficient_measurable g hg ((tensorRight (b j)).adjoint ψ))]
      simp only [packet_plancherel g hg]
    _ = _ := tensorRight_parseval a b ψ

lemma partialOccupation_integrable (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1)
    (ψ : Lp ℂ 2 ((volume : Measure V).prod ν)) :
    Integrable (partialOccupation g ψ) ((volume : Measure V).prod volume) := by
  have hp (p : V × V) : 0 ≤ partialOccupation g ψ p := sq_nonneg _
  have hm := partialOccupation_measurable g hg ψ
  have hm' : AEStronglyMeasurable (partialOccupation g ψ) ((volume : Measure V).prod volume) := by
    have h := hm.ennreal_toReal.aestronglyMeasurable
    simpa only [Function.comp_def, ENNReal.toReal_ofReal (hp _)] using h
  refine ⟨hm', ?_⟩
  rw [HasFiniteIntegral]
  simp only [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hp _)]
  rw [partialOccupation_mass g hg]
  exact ENNReal.ofReal_lt_top

lemma partialOccupation_integral (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1)
    (ψ : Lp ℂ 2 ((volume : Measure V).prod ν)) :
    (∫ p, partialOccupation g ψ p ∂((volume : Measure V).prod volume)) = ‖ψ‖^2 := by
  have h := partialOccupation_mass g hg ψ
  rw [← ofReal_integral_eq_lintegral_ofReal (partialOccupation_integrable g hg ψ)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)] at h
  exact (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg fun _ => sq_nonneg _) (sq_nonneg _)).1 h

end

open CoulombPauli

def spinVector (s : Fin 2) : Lp ℂ 2 (Measure.count : Measure (Fin 2)) :=
  indicatorConstLp 2 (measurableSet_singleton s) (by simp) 1

lemma spinVector_inner (s : Fin 2) (u : Lp ℂ 2 (Measure.count : Measure (Fin 2))) :
    inner ℂ (spinVector s) u = u s := by
  rw [spinVector, L2.inner_indicatorConstLp_one]
  simp

lemma spinVector_orthonormal : Orthonormal ℂ spinVector := by
  classical
  rw [orthonormal_iff_ite]
  intro s t
  rw [spinVector, spinVector, L2.inner_indicatorConstLp_one_indicatorConstLp_one]
  by_cases h : s = t
  · subst t; simp
  · have hd : ({s} : Set (Fin 2)) ∩ {t} = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨rfl,rfl⟩; exact h rfl
    simp [hd,h]

def spinBasis : HilbertBasis (Fin 2) ℂ (Lp ℂ 2 (Measure.count : Measure (Fin 2))) :=
  HilbertBasis.mkOfOrthogonalEqBot spinVector_orthonormal (by
    apply le_antisymm _ bot_le
    intro u hu
    change u = 0
    have hv (s : Fin 2) : u s = 0 := by
      rw [← spinVector_inner]
      exact Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_range_self s)) hu
    apply Lp.ext
    filter_upwards [Lp.coeFn_zero ℂ 2 (Measure.count : Measure (Fin 2))] with s hs
    rw [hv, hs, Pi.zero_apply])

lemma spinBasis_apply (s : Fin 2) : spinBasis s = spinVector s := by
  simp [spinBasis]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

abbrev spinSpaceMeasure : Measure (V × Fin 2) := (volume : Measure V).prod Measure.count

def spinPacket (g : 𝓢(V, ℝ)) (s : Fin 2) (p : V × V) : Lp ℂ 2 (spinSpaceMeasure (V := V)) :=
  tensor (packet g p) (spinBasis s)

lemma spinPacket_norm (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1) (s : Fin 2) (p : V × V) :
    ‖spinPacket g s p‖ = 1 := by
  rw [spinPacket, tensor_norm, spinBasis.orthonormal.norm_eq_one, mul_one]
  have h := packet_norm_sq g p
  rw [hg] at h
  nlinarith [norm_nonneg (packet g p)]

lemma spinPacket_coefficient (g : 𝓢(V, ℝ)) (s : Fin 2) (p : V × V)
    (u : Lp ℂ 2 (spinSpaceMeasure (V := V))) :
    inner ℂ (spinPacket g s p) u = inner ℂ (packet g p) ((tensorRight (spinBasis s)).adjoint u) := by
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

lemma spinPacket_plancherel (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1)
    (u : Lp ℂ 2 (spinSpaceMeasure (V := V))) :
    (∑ s : Fin 2, ∫⁻ p, ENNReal.ofReal (‖inner ℂ (spinPacket g s p) u‖^2)
      ∂((volume : Measure V).prod volume)) = ENNReal.ofReal (‖u‖^2) := by
  obtain ⟨w,a,-⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 (volume : Measure V))
  simp_rw [spinPacket_coefficient, packet_plancherel g hg]
  simpa only [tsum_fintype] using tensorRight_parseval a spinBasis u

end CoulombPackets

end

end OAI
