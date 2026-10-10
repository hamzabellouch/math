import OAI.Analysis.FactorGeneration.QuotientHilbert

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Exact coordinate centering in projection corners whose traces have a
uniform positive lower bound. The corner scalar is divided by its actual
trace; no global-centering-to-corner-centering implication is assumed. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem corner_trace_norm_lower (f : Bounded M) (δ : ℝ)
    (hlower : ∀ j,δ ≤ (τ.trace (f.val j)).re) (j : ℕ) :
    δ ≤ ‖τ.trace (f.val j)‖ := (hlower j).trans (Complex.re_le_norm _)

def boundedCornerScalar (f b : Bounded M) (hf : ∀ j,IsStarProjection (f.val j))
    (δ : ℝ) (hδ : 0 < δ) (hlower : ∀ j,δ ≤ (τ.trace (f.val j)).re) : Bounded M :=
  ⟨fun j => (τ.trace (b.val j)/τ.trace (f.val j)) • f.val j,by
    obtain ⟨C,hC,hb⟩ := b.property
    refine ⟨C/δ,div_nonneg hC hδ.le,fun j => ?_⟩
    rw [norm_smul]
    apply (mul_le_of_le_one_right (norm_nonneg _) (hf j).norm_le).trans
    rw [norm_div]
    exact div_le_div₀ hC
      (((τ.norm_trace_le_norm₂ _).trans (τ.norm₂_le_norm _)).trans (hb j))
      hδ (corner_trace_norm_lower τ f δ hlower j)⟩

def boundedCornerCenter (f a : Bounded M) (hf : ∀ j,IsStarProjection (f.val j))
    (δ : ℝ) (hδ : 0 < δ) (hlower : ∀ j,δ ≤ (τ.trace (f.val j)).re) : Bounded M :=
  f*a*f-boundedCornerScalar τ f (f*a*f) hf δ hδ hlower

theorem boundedCornerCenter_trace (f a : Bounded M) (hf : ∀ j,IsStarProjection (f.val j))
    (δ : ℝ) (hδ : 0 < δ) (hlower : ∀ j,δ ≤ (τ.trace (f.val j)).re) (j : ℕ) :
    τ.trace ((boundedCornerCenter τ f a hf δ hδ hlower).val j)=0 := by
  have hne : τ.trace (f.val j) ≠ 0 := by
    intro h
    have := hlower j
    rw [h,Complex.zero_re] at this
    linarith
  change τ.trace (f.val j*a.val j*f.val j -
    (τ.trace (f.val j*a.val j*f.val j)/τ.trace (f.val j)) • f.val j)=0
  rw [TracialRepresentation.trace_sub,TracialRepresentation.trace_smul,div_mul_cancel₀ _ hne,sub_self]

theorem boundedCornerCenter_supported (f a : Bounded M) (hf : ∀ j,IsStarProjection (f.val j))
    (δ : ℝ) (hδ : 0 < δ) (hlower : ∀ j,δ ≤ (τ.trace (f.val j)).re) :
    f*boundedCornerCenter τ f a hf δ hδ hlower=boundedCornerCenter τ f a hf δ hδ hlower ∧
    boundedCornerCenter τ f a hf δ hδ hlower*f=boundedCornerCenter τ f a hf δ hδ hlower := by
  constructor <;> apply Subtype.ext <;> funext j
  · change f.val j*(f.val j*a.val j*f.val j - _ • f.val j)=_
    simp only [mul_sub,← mul_assoc,mul_smul_comm,(hf j).isIdempotentElem.eq]
    rfl
  · change (f.val j*a.val j*f.val j - _ • f.val j)*f.val j=_
    simp only [sub_mul,mul_assoc,smul_mul_assoc,(hf j).isIdempotentElem.eq]
    rfl

theorem boundedCornerCenter_quotient (ω : Ultrafilter ℕ)
    (f a : Bounded M) (hf : ∀ j,IsStarProjection (f.val j))
    (δ : ℝ) (hδ : 0 < δ) (hlower : ∀ j,δ ≤ (τ.trace (f.val j)).re)
    (hz : quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (f*a*f))=0) :
    quotientMap τ (ω : Filter ℕ) (boundedCornerCenter τ f a hf δ hδ hlower)=
      quotientMap τ (ω : Filter ℕ) (f*a*f) := by
  apply (quotientMap_eq_iff τ (ω : Filter ℕ) _ _).mpr
  let b := f*a*f
  have ht := ((traceRep_tendsto τ ω b).norm).div_const δ
  change traceRep τ ω b=0 at hz
  rw [hz,norm_zero,zero_div] at ht
  change Tendsto (fun j => τ.norm₂ ((boundedCornerCenter τ f a hf δ hδ hlower).val j - b.val j)) _ _
  apply squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) ht
  have he : (boundedCornerCenter τ f a hf δ hδ hlower).val j - b.val j =
      -((τ.trace (b.val j)/τ.trace (f.val j)) • f.val j) := by
    change (b.val j - _)-b.val j = _
    abel
  rw [he]
  have hn : τ.norm₂ (-((τ.trace (b.val j)/τ.trace (f.val j)) • f.val j)) =
      ‖τ.trace (b.val j)/τ.trace (f.val j)‖*τ.norm₂ (f.val j) := by
    change ‖-((τ.trace (b.val j)/τ.trace (f.val j)) • ((f.val j : H →L[ℂ] H) τ.vector))‖ = _
    rw [norm_neg,norm_smul]
    rfl
  change τ.norm₂ (-((τ.trace (b.val j)/τ.trace (f.val j)) • f.val j)) ≤ _
  rw [hn]
  apply (mul_le_of_le_one_right (norm_nonneg _) ((τ.norm₂_le_norm _).trans (hf j).norm_le)).trans
  rw [norm_div]
  exact div_le_div₀ (norm_nonneg _) le_rfl hδ (corner_trace_norm_lower τ f δ hlower j)

end

/-! A projection sequence of positive quotient trace can be changed on an
ultrafilter-null set so every coordinate corner has uniformly positive trace.
Coordinates are replaced only by the unit, preserving subalgebra membership. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem quotientMap_eq_of_eventuallyEq (l : Filter ℕ) (a b : Bounded M)
    (he : a.val =ᶠ[l] b.val) : quotientMap τ l a=quotientMap τ l b := by
  apply (quotientMap_eq_iff τ l a b).mpr
  have hh : (fun _ : ℕ => (0 : ℝ)) =ᶠ[l] (fun j => τ.norm₂ (a.val j-b.val j)) := by
    filter_upwards [he] with j hj
    rw [hj,sub_self,τ.norm₂_zero]
  exact tendsto_const_nhds.congr' hh

theorem exists_uniform_positive_corner_representative (ω : Ultrafilter ℕ)
    (f : Bounded M) (hf : ∀ j,IsStarProjection (f.val j))
    (ht : 0 < (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) f)).re) :
    ∃ δ : ℝ,0 < δ ∧ ∃ g : Bounded M,
      (∀ j,IsStarProjection (g.val j)) ∧ (∀ j,δ ≤ (τ.trace (g.val j)).re) ∧
      quotientMap τ (ω : Filter ℕ) g=quotientMap τ (ω : Filter ℕ) f ∧
      (∀ j,g.val j=f.val j ∨ g.val j=1) := by
  classical
  let t := (traceRep τ ω f).re
  change 0 < t at ht
  let δ : ℝ := min (t/2) (1/2)
  have hδ : 0 < δ := lt_min (half_pos ht) (by norm_num)
  have hδt : δ < t := (min_le_left _ _).trans_lt (half_lt_self ht)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  let g : Bounded M := ⟨fun j => if δ ≤ (τ.trace (f.val j)).re then f.val j else 1,
    1,zero_le_one,fun j => by
      change ‖if δ ≤ (τ.trace (f.val j)).re then f.val j else 1‖ ≤ 1
      split_ifs
      · exact (hf j).norm_le
      · exact operator_norm_one_le⟩
  refine ⟨δ,hδ,g,?_,?_,?_,?_⟩
  · intro j
    change IsStarProjection (if δ ≤ (τ.trace (f.val j)).re then f.val j else 1)
    split_ifs
    · exact hf j
    · exact IsStarProjection.one _
  · intro j
    change δ ≤ (τ.trace (if δ ≤ (τ.trace (f.val j)).re then f.val j else 1)).re
    split_ifs with h
    · exact h
    · simpa only [τ.trace_one,Complex.one_re] using hδ1
  · apply quotientMap_eq_of_eventuallyEq τ
    have he := (tendsto_order.mp
      (Complex.continuous_re.continuousAt.tendsto.comp (traceRep_tendsto τ ω f))).1 δ hδt
    filter_upwards [he] with j hj
    change δ < (τ.trace (f.val j)).re at hj
    change (if δ ≤ (τ.trace (f.val j)).re then f.val j else 1)=f.val j
    rw [ite_eq_left hj.le]
  · intro j
    change (if δ ≤ (τ.trace (f.val j)).re then f.val j else 1)=f.val j ∨
      (if δ ≤ (τ.trace (f.val j)).re then f.val j else 1)=1
    split_ifs <;> simp

end

/-! A projection sequence of positive quotient trace can be changed on an
ultrafilter-null set so every coordinate corner has uniformly positive trace.
Coordinates are replaced only by the unit, preserving subalgebra membership. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_eventually_positive_corner_representative (ω : Ultrafilter ℕ)
    (f : Bounded M) (hf : ∀ j,IsStarProjection (f.val j))
    (ht : 0 < (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) f)).re) :
    ∃ δ : ℝ,0 < δ ∧ ∃ g : Bounded M,
      (∀ j,IsStarProjection (g.val j)) ∧ (∀ j,δ ≤ (τ.trace (g.val j)).re) ∧
      g.val =ᶠ[(ω : Filter ℕ)] f.val ∧
      (∀ j,g.val j=f.val j ∨ g.val j=1) := by
  classical
  let t := (traceRep τ ω f).re
  change 0 < t at ht
  let δ : ℝ := min (t/2) (1/2)
  have hδ : 0 < δ := lt_min (half_pos ht) (by norm_num)
  have hδt : δ < t := (min_le_left _ _).trans_lt (half_lt_self ht)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  let g : Bounded M := ⟨fun j => if δ ≤ (τ.trace (f.val j)).re then f.val j else 1,
    1,zero_le_one,fun j => by
      change ‖if δ ≤ (τ.trace (f.val j)).re then f.val j else 1‖ ≤ 1
      split_ifs
      · exact (hf j).norm_le
      · exact operator_norm_one_le⟩
  refine ⟨δ,hδ,g,?_,?_,?_,?_⟩
  · intro j
    change IsStarProjection (if δ ≤ (τ.trace (f.val j)).re then f.val j else 1)
    split_ifs
    · exact hf j
    · exact IsStarProjection.one _
  · intro j
    change δ ≤ (τ.trace (if δ ≤ (τ.trace (f.val j)).re then f.val j else 1)).re
    split_ifs with h
    · exact h
    · simpa only [τ.trace_one,Complex.one_re] using hδ1
  · have he := (tendsto_order.mp
      (Complex.continuous_re.continuousAt.tendsto.comp (traceRep_tendsto τ ω f))).1 δ hδt
    filter_upwards [he] with j hj
    change δ < (τ.trace (f.val j)).re at hj
    change (if δ ≤ (τ.trace (f.val j)).re then f.val j else 1)=f.val j
    rw [ite_eq_left hj.le]
  · intro j
    change (if δ ≤ (τ.trace (f.val j)).re then f.val j else 1)=f.val j ∨
      (if δ ≤ (τ.trace (f.val j)).re then f.val j else 1)=1
    split_ifs <;> simp

theorem exists_eventually_centered_corner_representatives (ω : Ultrafilter ℕ)
    (f : Bounded M) (hf : ∀ j,IsStarProjection (f.val j))
    (ht : 0 < (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) f)).re)
    (x : ℕ → Q τ ω)
    (hx : ∀ i,quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) f*x i*
      quotientMap τ (ω : Filter ℕ) f)=0) :
    ∃ δ : ℝ,0 < δ ∧ ∃ g : Bounded M,
      (∀ j,IsStarProjection (g.val j)) ∧ (∀ j,δ ≤ (τ.trace (g.val j)).re) ∧
      g.val =ᶠ[(ω : Filter ℕ)] f.val ∧ (∀ j,g.val j=f.val j ∨ g.val j=1) ∧
      ∃ b : ℕ → Bounded M,∀ i,
        g*b i=b i ∧ b i*g=b i ∧ (∀ j,τ.trace ((b i).val j)=0) ∧
        quotientMap τ (ω : Filter ℕ) (b i)=
          quotientMap τ (ω : Filter ℕ) f*x i*quotientMap τ (ω : Filter ℕ) f := by
  classical
  obtain ⟨δ,hδ,g,hg,hgl,hgf,hgor⟩ :=
    exists_eventually_positive_corner_representative τ ω f hf ht
  have he := quotientMap_eq_of_eventuallyEq τ (ω : Filter ℕ) g f hgf
  choose a ha using fun i => quotientMap_surjective τ (ω : Filter ℕ) (x i)
  let b := fun i => boundedCornerCenter τ g (a i) hg δ hδ hgl
  refine ⟨δ,hδ,g,hg,hgl,hgf,hgor,b,fun i => ?_⟩
  have hclass : quotientMap τ (ω : Filter ℕ) (g*a i*g)=
      quotientMap τ (ω : Filter ℕ) f*x i*quotientMap τ (ω : Filter ℕ) f := by
    let q := quotientMap τ (ω : Filter ℕ)
    calc
      q ((g*a i)*g) = (q g*q (a i))*q g :=
        (map_mul q (g*a i) g).trans
          (congrArg (fun y : Q τ ω => y*q g) (map_mul q g (a i)))
      _ = q f*x i*q f :=
        congrArg₂ (fun y z : Q τ ω => y*z)
          (congrArg₂ (fun y z : Q τ ω => y*z) he (ha i)) he
  have hzero : quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (g*a i*g))=0 := by
    rw [hclass]
    exact hx i
  obtain ⟨hl,hr⟩ := boundedCornerCenter_supported τ g (a i) hg δ hδ hgl
  exact ⟨hl,hr,boundedCornerCenter_trace τ g (a i) hg δ hδ hgl,
    (boundedCornerCenter_quotient τ ω g (a i) hg δ hδ hgl hzero).trans hclass⟩

end

/-! Scalar normalization preserves exact corner support and centering. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_supported_centered_contraction (g b : Bounded M)
    (hl : g*b=b) (hr : b*g=b) (hc : ∀ j,τ.trace (b.val j)=0) :
    ∃ c : ℂ,c ≠ 0 ∧ ∃ a : Bounded M,
      g*a=a ∧ a*g=a ∧ (∀ j,‖a.val j‖ ≤ 1) ∧
      (∀ j,τ.trace (a.val j)=0) ∧ b=c • a := by
  obtain ⟨C,hC,hbound⟩ := b.property
  let r : ℝ := C+1
  have hpos : 0 < r := by dsimp [r]; linarith
  have hne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  refine ⟨(r : ℂ),hne,(r : ℂ)⁻¹ • b,?_,?_,?_,?_,?_⟩
  · rw [mul_smul_comm,hl]
  · rw [smul_mul_assoc,hr]
  · intro j
    change ‖(r : ℂ)⁻¹ • b.val j‖ ≤ 1
    rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpos]
    apply (inv_mul_le_iff₀ hpos).mpr
    simpa only [mul_one] using (hbound j).trans (by dsimp [r]; linarith)
  · intro j
    change τ.trace ((r : ℂ)⁻¹ • b.val j)=0
    rw [TracialRepresentation.trace_smul,hc j,mul_zero]
  · rw [smul_smul,mul_inv_cancel₀ hne,one_smul]

end Generator.Tracial

end

end OAI
