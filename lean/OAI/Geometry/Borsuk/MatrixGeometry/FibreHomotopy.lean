import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.FibreTransport
import OAI.Geometry.Borsuk.Support.ChamberPath
import OAI.Geometry.Borsuk.Support.PurityGeometry

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section FibreHomotopy
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

noncomputable def negativeCoordinates (f : E → ι → ℝ) (I : Finset ι) (Q : M) :
    EuclideanSpace ℝ ↥(Iᶜ : Finset ι) :=
  WithLp.toLp 2 (fun i => positiveExtension f Q i.val)

lemma Admissible.negativeCoordinates_sum {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} {u : E} (hu : u ∈ safeNormals (activeVectors f I))
    {Q : M} (hQ : Q ∈ matrixFibre u) :
    (∑ i, negativeCoordinates f I Q i) = 1 := by
  have hz : ∀ i ∈ I, positiveExtension f Q i = 0 := fun i hi =>
    hf.positiveExtension_safe_zero hu hQ.1 hQ.2.2 hi
  have hs := hf.positiveExtension_sum hQ.1
  rw [hQ.2.1] at hs
  have he : ∑ i : ↥(Iᶜ : Finset ι), positiveExtension f Q i.val =
      ∑ i : ι, positiveExtension f Q i := by
    rw [Finset.sum_coe_sort]
    exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hz i (by simpa using hi))
  exact he.trans hs

noncomputable def transportedFibre (c : E) (t : ℝ) (u : E) (Q : M) : M :=
  fibreTransport c u (chamberPath c u t) Q

noncomputable def centeredFibre (c u : E) (Q : M) : M :=
  matrixConjugate (householder c u) Q

omit [Nonempty ν] in
lemma centeredFibre_mem {c u : E} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1) {Q : M}
    (hQ : Q ∈ matrixFibre u) : centeredFibre c u Q ∈ matrixFibre c := by
  refine ⟨matrixConjugate_nonneg _ hQ.1,?_,?_⟩
  · rw [centeredFibre,matrixConjugate_trace,hQ.2.1]
  · simpa only [centeredFibre,householder_swap (hc.trans hu.symm)] using
      matrixConjugate_kernel (householder c u) hQ.2.2

omit [Nonempty ν] [DecidableEq ι] in
lemma transportedFibre_mem {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) {c u : E} (hc : c ∈ commonPositiveCone f I) (hcn : ‖c‖ = 1)
    (hun : ‖u‖ = 1) (hu : u ∈ signChamber (activeVectors f I) c)
    {t : ℝ} (ht : t ∈ Icc 0 1) {Q : M} (hQ : Q ∈ matrixFibre u) :
    transportedFibre c t u Q ∈ matrixFibre (chamberPath c u t) := by
  have hcs := hf.commonPositiveCone_safe I hc
  have hvn := chamberPath_norm (commonPositiveCone_active hI hc) hcs hu ht
  refine ⟨fibreTransport_nonneg _ _ _ hQ.1,?_,?_⟩
  · rw [transportedFibre,fibreTransport_trace,hQ.2.1]
  · exact fibreTransport_kernel (hcn.trans hun.symm) (hcn.trans hvn.symm) hQ.2.2

noncomputable def fibreHomotopy (f : E → ι → ℝ) (I : Finset ι) (c : E)
    (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (t : ℝ) (u : E) (Q : M) :=
  negativeCoordinates f I (transportedFibre c t u Q) +
    t • (g (centeredFibre c u Q) - negativeCoordinates f I (centeredFibre c u Q))

omit [Nonempty ν] in
lemma fibreHomotopy_zero (f : E → ι → ℝ) (I : Finset ι) (c : E)
    (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) {u : E} (hu : ‖u‖ = 1) (Q : M) :
    fibreHomotopy f I c g 0 u Q = negativeCoordinates f I Q := by
  simp only [fibreHomotopy,zero_smul,add_zero,transportedFibre,chamberPath_zero c u hu,
    fibreTransport_self]

omit [Nonempty ν] in
lemma fibreHomotopy_one (f : E → ι → ℝ) (I : Finset ι) {c u : E} (hc : ‖c‖ = 1)
    (hu : ‖u‖ = 1) (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) {Q : M}
    (hQ : Q ∈ matrixFibre u) : fibreHomotopy f I c g 1 u Q = g (centeredFibre c u Q) := by
  simp only [fibreHomotopy,one_smul,transportedFibre,chamberPath_one c u hc,
    fibreTransport_center hQ.1.isSelfAdjoint (hc.trans hu.symm) hQ.2.2]
  simp only [centeredFibre]
  abel

lemma Admissible.fibreHomotopy_sum {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) {c u : E} (hc : c ∈ commonPositiveCone f I) (hcn : ‖c‖ = 1)
    (hun : ‖u‖ = 1) (hu : u ∈ signChamber (activeVectors f I) c)
    (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι))
    (hg : ∀ Q ∈ matrixFibre c, ∑ i, g Q i = 1)
    {t : ℝ} (ht : t ∈ Icc 0 1) {Q : M} (hQ : Q ∈ matrixFibre u) :
    (∑ i, fibreHomotopy f I c g t u Q i) = 1 := by
  have hcs := hf.commonPositiveCone_safe I hc
  have hvs := signChamber_subset_safeNormals _ _ (chamberPath_mem (commonPositiveCone_active hI hc) hcs hu ht)
  have hT := transportedFibre_mem hf hI hc hcn hun hu ht hQ
  have hC := centeredFibre_mem hcn hun hQ
  simp only [fibreHomotopy,PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul,
    Finset.sum_add_distrib]
  rw [← Finset.mul_sum,Finset.sum_sub_distrib]
  rw [hf.negativeCoordinates_sum hvs hT,hg _ hC,hf.negativeCoordinates_sum hcs hC]
  ring

lemma Admissible.fibreHomotopy_boundary_misses {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (hI : I.Nonempty) {c u : E} (hc : c ∈ commonPositiveCone f I)
    (hcn : ‖c‖ = 1) (hun : ‖u‖ = 1) (hu : u ∈ signChamber (activeVectors f I) c)
    (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) {ε : ℝ} (hε : 0 < ε)
    (hg : ∀ Q ∈ matrixFibre c, ‖g Q - negativeCoordinates f I Q‖ < ε)
    (z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (hz : ∀ i, ε < z i)
    {t : ℝ} (ht : t ∈ Icc 0 1) {Q : M} (hQ : Q ∈ matrixFibre u)
    (hn : ¬ IsUnit (rankOne u + Q)) : fibreHomotopy f I c g t u Q ≠ z := by
  have hcs := hf.commonPositiveCone_safe I hc
  have hvmem := chamberPath_mem (commonPositiveCone_active hI hc) hcs hu ht
  have hvn := chamberPath_norm (commonPositiveCone_active hI hc) hcs hu ht
  have hT := transportedFibre_mem hf hI hc hcn hun hu ht hQ
  have htn : ¬ IsUnit (rankOne (chamberPath c u t) + transportedFibre c t u Q) := by
    intro h
    exact hn ((fibreTransport_unit_iff (hcn.trans hun.symm) (hcn.trans hvn.symm)).mp h)
  obtain ⟨i,hi,hzi⟩ := hf.fibre_boundary_missing (signChamber_subset_safeNormals _ _ hvmem) hT.1 htn
  let j : ↥(Iᶜ : Finset ι) := ⟨i,hi⟩
  have hC := centeredFibre_mem hcn hun hQ
  have hb : |(g (centeredFibre c u Q) - negativeCoordinates f I (centeredFibre c u Q)) j| < ε :=
    lt_of_le_of_lt (by simpa only [Real.norm_eq_abs] using
      (PiLp.norm_apply_le (g (centeredFibre c u Q) - negativeCoordinates f I (centeredFibre c u Q)) j)) (hg _ hC)
  intro he
  have hj := congrArg (fun v : EuclideanSpace ℝ ↥(Iᶜ : Finset ι) => v j) he
  change positiveExtension f (transportedFibre c t u Q) i +
    t * ((g (centeredFibre c u Q) - negativeCoordinates f I (centeredFibre c u Q)) j) = z j at hj
  rw [hzi,zero_add] at hj
  have hjb := hz j
  have hab := abs_lt.mp hb
  have hle := mul_le_mul_of_nonneg_left hab.2.le ht.1
  have hh : t * ε ≤ ε := by nlinarith [ht.2]
  linarith

end FibreHomotopy
end BorsukNine

end OAI
