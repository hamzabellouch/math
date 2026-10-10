import OAI.Analysis.FactorGeneration.Pinching
import OAI.Analysis.FactorGeneration.Supports
import OAI.Analysis.FactorGeneration.UnitaryMetric

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Positivity of the tracial pairing does not require the two positive
operators to commute. These estimates will control spectral truncation. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
local instance tracePairingCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance tracePairingOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance tracePairingPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance tracePairingLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance tracePairingStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem trace_mul_nonneg (a b : M.toStarSubalgebra) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ (τ.trace (a*b)).re := by
  let s := CFC.sqrt a
  have hs : star s=s := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  have h := trace_nonneg_of_nonneg τ (star s*b*s) (star_left_conjugate_nonneg hb s)
  rw [hs,τ.trace_mul_comm (s*b) s,← mul_assoc,CFC.sqrt_mul_sqrt_self a ha] at h
  exact h

theorem trace_mul_mono (a b c : M.toStarSubalgebra) (ha : 0 ≤ a) (hbc : b ≤ c) :
    (τ.trace (a*b)).re ≤ (τ.trace (a*c)).re := by
  have h := trace_mul_nonneg τ a (c-b) ha (sub_nonneg.mpr hbc)
  rw [mul_sub,trace_sub,Complex.sub_re] at h
  linarith

theorem trace_mul_le_norm (a x : M.toStarSubalgebra) (ha : 0 ≤ a)
    (hx : IsSelfAdjoint x) :
    (τ.trace (a*x)).re ≤ ‖x‖ * (τ.trace a).re := by
  have h := trace_mul_mono τ a x (algebraMap ℝ M.toStarSubalgebra ‖x‖) ha
    hx.le_algebraMap_norm_self
  rw [Algebra.algebraMap_eq_smul_one,mul_smul_comm,mul_one,← Complex.coe_smul,
    cornerTrace_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at h
  exact h

theorem norm₂_sub_sq (x y : M.toStarSubalgebra) :
    τ.norm₂ (x-y)^2 = τ.norm₂ x^2 + τ.norm₂ y^2 -
      2*(τ.trace (star x*y)).re := by
  have h := norm_sub_sq (𝕜 := ℂ) (baseVector τ x) (baseVector τ y)
  rw [← map_sub,baseVector_inner_trace] at h
  change τ.norm₂ (x-y)^2 = τ.norm₂ x^2 - 2*(τ.trace (star x*y)).re + τ.norm₂ y^2 at h
  linarith

end

/-! Upper spectral truncation of a self-adjoint operator. The truncation
remains in the original operator ball and has a positive discarded part. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance truncationCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance truncationOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance truncationLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance truncationStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

def upperTruncate (a : M.toStarSubalgebra) (C : ℝ) : M.toStarSubalgebra :=
  a-(a-algebraMap ℝ M.toStarSubalgebra C)⁺

theorem upperTruncate_cfc (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (C : ℝ) :
    upperTruncate a C = cfc (fun t : ℝ => min t C) a := by
  have hf : (fun t : ℝ => min t C) = fun t => t-(t-C)⁺ := by
    funext t
    simp only [_root_.posPart_def]
    by_cases h : t ≤ C
    · rw [min_eq_left h,max_eq_right (sub_nonpos.mpr h),sub_zero]
    · rw [min_eq_right (le_of_not_ge h),max_eq_left (sub_nonneg.mpr (le_of_not_ge h))]
      ring
  rw [hf,cfc_sub (fun t : ℝ => t) (fun t => (t-C)⁺) a,cfc_id' ℝ a]
  unfold upperTruncate
  congr 1
  rw [CFC.posPart_def,cfcₙ_eq_cfc]
  have hs : cfc (fun t : ℝ => t-C) a = a-algebraMap ℝ M.toStarSubalgebra C := by
    rw [cfc_sub (fun t : ℝ => t) (fun _ => C) a,cfc_id' ℝ a,cfc_const C a ha]
  rw [← hs,← cfc_comp (fun t : ℝ => t⁺) (fun t => t-C) a]
  rfl

theorem upperTruncate_selfAdjoint (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (C : ℝ) :
    IsSelfAdjoint (upperTruncate a C) :=
  ha.sub (CFC.posPart_nonneg _).isSelfAdjoint

theorem upperTruncate_norm_le (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a)
    (C R : ℝ) (hC : 0 ≤ C) (hR : ‖a‖ ≤ R) : ‖upperTruncate a C‖ ≤ R := by
  obtain (hH | hH) := subsingleton_or_nontrivial H
  · have ha0 : a=0 := Subtype.ext (Subsingleton.elim _ _)
    have hz : upperTruncate a C=0 := Subtype.ext (Subsingleton.elim _ _)
    simpa only [hz,norm_zero] using (norm_nonneg a).trans hR
  rw [upperTruncate_cfc a ha C]
  apply norm_cfc_le ((norm_nonneg a).trans hR)
  intro t ht
  have htR := (spectrum.norm_le_norm_of_mem ht).trans hR
  rw [Real.norm_eq_abs,abs_le] at htR ⊢
  exact ⟨le_min htR.1 (by linarith), (min_le_left _ _).trans htR.2⟩

theorem upperTruncate_discard_mul (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (C : ℝ) :
    (a-algebraMap ℝ M.toStarSubalgebra C)⁺ * upperTruncate a C =
      C • (a-algebraMap ℝ M.toStarSubalgebra C)⁺ := by
  let b := a-algebraMap ℝ M.toStarSubalgebra C
  have hb : IsSelfAdjoint b := ha.sub (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all C))
  have he : upperTruncate a C = algebraMap ℝ M.toStarSubalgebra C-b⁻ := by
    have hh := CFC.posPart_sub_negPart b hb
    have heq : a=b+algebraMap ℝ M.toStarSubalgebra C := by dsimp [b]; abel
    change a-b⁺=algebraMap ℝ M.toStarSubalgebra C-b⁻
    nth_rw 1 [heq]
    nth_rw 1 [← hh]
    abel
  rw [he,mul_sub,CFC.posPart_mul_negPart,sub_zero,
    Algebra.algebraMap_eq_smul_one,mul_smul_comm,mul_one]

theorem upperTruncate_distance (τ : TracialRepresentation M)
    (a x : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (hx : IsSelfAdjoint x) :
    τ.norm₂ (upperTruncate a ‖x‖-x)^2 +
      τ.norm₂ ((a-algebraMap ℝ M.toStarSubalgebra ‖x‖)⁺)^2 ≤ τ.norm₂ (a-x)^2 := by
  let d := (a-algebraMap ℝ M.toStarSubalgebra ‖x‖)⁺
  let z := upperTruncate a ‖x‖
  have hd : 0 ≤ d := CFC.posPart_nonneg _
  have had : a=z+d := by dsimp [z,d,upperTruncate]; abel
  have hdz : d*z=‖x‖ • d := upperTruncate_discard_mul a ha ‖x‖
  have ht := trace_mul_le_norm τ d x hd hx
  have hsq := norm₂_sub_sq τ (a-x) d
  have hid : a-x-d=z-x := by rw [had]; abel
  rw [hid,(ha.sub hx).star_eq,τ.trace_mul_comm (a-x) d] at hsq
  have htrace : (τ.trace (d*(a-x))).re =
      τ.norm₂ d^2+‖x‖*(τ.trace d).re-(τ.trace (d*x)).re := by
    rw [had,mul_sub,mul_add,trace_sub,cornerTrace_add,hdz,← Complex.coe_smul,
      cornerTrace_smul,Complex.sub_re,Complex.add_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [norm₂_sq_trace τ,hd.isSelfAdjoint.star_eq]
    ring
  rw [htrace] at hsq
  change τ.norm₂ (z-x)^2 + τ.norm₂ d^2 ≤ τ.norm₂ (a-x)^2
  linarith

end

/-! Spectral truncation forces a self-adjoint least-distance point in a
subalgebra ball to have norm at most the norm of the ambient test operator. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}
local instance interiorCStar (A : VonNeumannAlgebra H) : CStarAlgebra A.toStarSubalgebra := {}
local instance interiorOrder (A : VonNeumannAlgebra H) : PartialOrder A.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance interiorPreorder (A : VonNeumannAlgebra H) : Preorder A.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance interiorLE (A : VonNeumannAlgebra H) : LE A.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toLE
local instance interiorStarOrder (A : VonNeumannAlgebra H) : StarOrderedRing A.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem included_selfAdjoint (hNM : N ≤ M) (a : N.toStarSubalgebra) (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (coordinateInclusion hNM a) := by
  change star (coordinateInclusion hNM a)=coordinateInclusion hNM a
  rw [← map_star,ha.star_eq]

theorem included_upperTruncate (hNM : N ≤ M) (a : N.toStarSubalgebra)
    (ha : IsSelfAdjoint a) (C : ℝ) :
    coordinateInclusion hNM (upperTruncate a C)=upperTruncate (coordinateInclusion hNM a) C := by
  rw [upperTruncate_cfc a ha C,
    upperTruncate_cfc _ (included_selfAdjoint hNM a ha) C]
  exact (coordinateInclusion hNM).map_cfc (fun t : ℝ => min t C) a
    (by fun_prop) (by fun_prop) ha (included_selfAdjoint hNM a ha)

theorem selfAdjoint_norm_le_of_bounds (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a)
    (C : ℝ) (hC : 0 ≤ C) (hu : a ≤ algebraMap ℝ M.toStarSubalgebra C)
    (hl : -a ≤ algebraMap ℝ M.toStarSubalgebra C) : ‖a‖ ≤ C := by
  obtain (hA | hA) := subsingleton_or_nontrivial M.toStarSubalgebra
  · simpa only [Subsingleton.elim a 0,norm_zero] using hC
  have hpos : ∀ t ∈ spectrum ℝ a,t ≤ C := by
    apply (cfc_le_iff (fun t : ℝ => t) (fun _ => C) a).mp
    rw [cfc_id' ℝ a ha,cfc_const C a ha]
    exact hu
  have hneg : ∀ t ∈ spectrum ℝ a,-t ≤ C := by
    apply (cfc_le_iff (fun t : ℝ => -t) (fun _ => C) a).mp
    rw [cfc_neg (fun t : ℝ => t) a,cfc_id' ℝ a ha,cfc_const C a ha]
    exact hl
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum a ha with h | h
  · exact hpos _ h
  · simpa using hneg _ h

theorem selfAdjoint_ball_minimum_upper (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (R : ℝ)
    (c : N.toStarSubalgebra) (hc : IsSelfAdjoint c) (hcR : ‖c‖ ≤ R)
    (hmin : ∀ a : N.toStarSubalgebra, IsSelfAdjoint a → ‖a‖ ≤ R →
      τ.norm₂ (x-coordinateInclusion hNM c) ≤ τ.norm₂ (x-coordinateInclusion hNM a)) :
    coordinateInclusion hNM c ≤ algebraMap ℝ M.toStarSubalgebra ‖x‖ := by
  have hz := hmin (upperTruncate c ‖x‖) (upperTruncate_selfAdjoint c hc ‖x‖)
    (upperTruncate_norm_le c hc ‖x‖ R (norm_nonneg _) hcR)
  rw [included_upperTruncate hNM c hc] at hz
  have hd := upperTruncate_distance τ (coordinateInclusion hNM c) x
    (included_selfAdjoint hNM c hc) hx
  have hrev (a b : M.toStarSubalgebra) : τ.norm₂ (a-b)=τ.norm₂ (b-a) := norm_sub_rev _ _
  rw [hrev x,hrev x] at hz
  have he : τ.norm₂ ((coordinateInclusion hNM c-algebraMap ℝ M.toStarSubalgebra ‖x‖)⁺)=0 := by
    nlinarith [show 0 ≤ τ.norm₂ (coordinateInclusion hNM c-x) from norm_nonneg _,
      show 0 ≤ τ.norm₂ (upperTruncate (coordinateInclusion hNM c) ‖x‖-x) from norm_nonneg _,
      show 0 ≤ τ.norm₂ ((coordinateInclusion hNM c-algebraMap ℝ M.toStarSubalgebra ‖x‖)⁺) from norm_nonneg _]
  exact sub_nonpos.mp ((CFC.posPart_eq_zero_iff _
    ((included_selfAdjoint hNM c hc).sub (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all ‖x‖)))).mp
      ((τ.norm₂_eq_zero_iff _).mp he))

theorem selfAdjoint_ball_minimum_norm (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (R : ℝ)
    (c : N.toStarSubalgebra) (hc : IsSelfAdjoint c) (hcR : ‖c‖ ≤ R)
    (hmin : ∀ a : N.toStarSubalgebra, IsSelfAdjoint a → ‖a‖ ≤ R →
      τ.norm₂ (x-coordinateInclusion hNM c) ≤ τ.norm₂ (x-coordinateInclusion hNM a)) :
    ‖c‖ ≤ ‖x‖ := by
  have hu := selfAdjoint_ball_minimum_upper τ hNM x hx R c hc hcR hmin
  have hn := selfAdjoint_ball_minimum_upper τ hNM (-x) hx.neg R (-c) hc.neg
    (by simpa using hcR) (by
      intro a ha hRa
      have h := hmin (-a) ha.neg (by simpa using hRa)
      have hneg (b : M.toStarSubalgebra) : τ.norm₂ (-b)=τ.norm₂ b := norm_neg _
      rw [map_neg,show -x- -(coordinateInclusion hNM c)=-(x-coordinateInclusion hNM c) by abel,
        show -x-coordinateInclusion hNM a=-(x-coordinateInclusion hNM (-a)) by rw [map_neg]; abel,
        hneg,hneg]
      exact h)
  rw [map_neg,norm_neg] at hn
  exact selfAdjoint_norm_le_of_bounds _ (included_selfAdjoint hNM c hc) ‖x‖ (norm_nonneg _) hu hn

end

/-! Two-sided spectral clipping and trace-norm control. The auxiliary trace
is explicit; the trace-free construction supplies it on its actual closure. -/
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance clippingCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance clippingOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance clippingStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

def traceSymmetrize (a : M.toStarSubalgebra) : M.toStarSubalgebra :=
  (2 : ℂ)⁻¹ • (a+star a)

theorem traceSymmetrize_selfAdjoint (a : M.toStarSubalgebra) : IsSelfAdjoint (traceSymmetrize a) := by
  change star ((2 : ℂ)⁻¹ • (a+star a)) = (2 : ℂ)⁻¹ • (a+star a)
  simp [add_comm]

theorem traceSymmetrize_eq_self (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) :
    traceSymmetrize a = a := by
  simp only [traceSymmetrize,ha.star_eq,← two_smul ℂ a,smul_smul]
  norm_num

theorem traceSymmetrize_sub (a b : M.toStarSubalgebra) :
    traceSymmetrize (a-b) = traceSymmetrize a-traceSymmetrize b := by
  simp only [traceSymmetrize,star_sub,smul_add,smul_sub]
  abel

theorem traceSymmetrize_norm₂_le (τ : TracialRepresentation M) (a : M.toStarSubalgebra) :
    τ.norm₂ (traceSymmetrize a) ≤ τ.norm₂ a := by
  rw [traceSymmetrize,τ.norm₂_smul,norm_inv]
  norm_num only [Complex.norm_ofNat]
  have h := τ.norm₂_add_le a (star a)
  rw [τ.norm₂_star] at h
  linarith

def traceClip (a : M.toStarSubalgebra) (C : ℝ) : M.toStarSubalgebra :=
  -upperTruncate (-upperTruncate a C) C

theorem traceClip_selfAdjoint (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (C : ℝ) :
    IsSelfAdjoint (traceClip a C) :=
  (upperTruncate_selfAdjoint _ (upperTruncate_selfAdjoint a ha C).neg C).neg

theorem traceClip_cfc (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (C : ℝ) :
    traceClip a C = cfc (fun t : ℝ => -min (-min t C) C) a := by
  rw [traceClip,upperTruncate_cfc _ (upperTruncate_selfAdjoint a ha C).neg C,
    upperTruncate_cfc a ha C,← cfc_neg (fun t : ℝ => min t C) a,
    ← cfc_comp (fun t : ℝ => min t C) (fun t : ℝ => -min t C) a]
  simp only [Function.comp_def]
  rw [cfc_neg (fun t : ℝ => min (-min t C) C) a]

theorem traceClip_norm_le (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a)
    (C : ℝ) (hC : 0 ≤ C) : ‖traceClip a C‖ ≤ C := by
  rw [traceClip_cfc a ha C]
  apply norm_cfc_le hC
  intro t _
  rw [Real.norm_eq_abs,abs_le]
  constructor
  · exact neg_le_neg (min_le_right _ _)
  · have h : -C ≤ min (-min t C) C :=
      le_min (neg_le_neg (min_le_right _ _)) (by linarith)
    linarith

theorem traceClip_distance (τ : TracialRepresentation M) (a x : M.toStarSubalgebra)
    (ha : IsSelfAdjoint a) (hx : IsSelfAdjoint x) :
    τ.norm₂ (traceClip a ‖x‖-x) ≤ τ.norm₂ (a-x) := by
  have h₁ := upperTruncate_distance τ a x ha hx
  have h₂ := upperTruncate_distance τ (-upperTruncate a ‖x‖) (-x)
    (upperTruncate_selfAdjoint a ha ‖x‖).neg hx.neg
  rw [norm_neg] at h₂
  have hn (b : M.toStarSubalgebra) : τ.norm₂ (-b) = τ.norm₂ b := norm_neg _
  have he : traceClip a ‖x‖-x = -(upperTruncate (-upperTruncate a ‖x‖) ‖x‖-(-x)) := by
    dsimp [traceClip]; abel
  have he' : -upperTruncate a ‖x‖-(-x) = -(upperTruncate a ‖x‖-x) := by abel
  rw [he',hn] at h₂
  rw [he,hn]
  have hnonneg : 0 ≤ τ.norm₂ (a-x) := norm_nonneg _
  nlinarith [sq_nonneg (τ.norm₂ ((a-algebraMap ℝ M.toStarSubalgebra ‖x‖)⁺)),
    sq_nonneg (τ.norm₂ ((-upperTruncate a ‖x‖-algebraMap ℝ M.toStarSubalgebra ‖x‖)⁺))]

end Generator.Tracial

end

end OAI
