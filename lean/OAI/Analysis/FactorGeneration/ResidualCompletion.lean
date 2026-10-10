import OAI.Analysis.FactorGeneration.CornerIndependence
import OAI.Analysis.FactorGeneration.QuotientCorners
import OAI.Analysis.FactorGeneration.QuotientRepresentation
import OAI.Analysis.FactorGeneration.ResidualMoments

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual residual projections, null-set masking, and coordinatewise
orthogonal partial-unitary patching. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def boundedPartialResidual (v : ℕ → PartialUnitary M) : Bounded M :=
  1-boundedPartialSupport v

theorem boundedPartialResidual_projection (v : ℕ → PartialUnitary M) (j : ℕ) :
    IsStarProjection ((boundedPartialResidual v).val j) := (v j).support.property.one_sub

theorem boundedPartialResidual_mem (v : ℕ → PartialUnitary M)
    (hv : ∀ j,(v j).val.val ∈ N) (j : ℕ) :
    ((boundedPartialResidual v).val j).val ∈ N := by
  have hs : (v j).support.val.val ∈ N := by
    rw [← (v j).unitary.initial]
    have hstar : star ((v j).val.val) ∈ N.toStarSubalgebra :=
      star_mem (show (v j).val.val ∈ N.toStarSubalgebra from hv j)
    exact N.mul_mem hstar (hv j)
  exact N.sub_mem N.one_mem hs

def maskPartialSequence (S : Set ℕ) (v : ℕ → PartialUnitary M) : ℕ → PartialUnitary M :=
  fun j => @ite (PartialUnitary M) (j ∈ S) (Classical.propDecidable _) (v j) zeroPartialUnitary

theorem maskPartialSequence_quotient (τ : TracialRepresentation M) (l : Filter ℕ)
    (S : Set ℕ) (hS : S ∈ l) (v : ℕ → PartialUnitary M) :
    quotientMap τ l (boundedPartialUnitary (maskPartialSequence S v))=
      quotientMap τ l (boundedPartialUnitary v) ∧
    quotientMap τ l (boundedPartialSupport (maskPartialSequence S v))=
      quotientMap τ l (boundedPartialSupport v) := by
  constructor
  · apply quotientMap_eq_of_eventuallyEq τ
    filter_upwards [hS] with j hj
    change (maskPartialSequence S v j).val=(v j).val
    simp only [maskPartialSequence,ite_eq_left hj]
  · apply quotientMap_eq_of_eventuallyEq τ
    filter_upwards [hS] with j hj
    change (maskPartialSequence S v j).support.val=(v j).support.val
    simp only [maskPartialSequence,ite_eq_left hj]

theorem maskPartialSequence_mem (S : Set ℕ) (v : ℕ → PartialUnitary M)
    (hv : ∀ j,(v j).val.val ∈ N) : ∀ j,(maskPartialSequence S v j).val.val ∈ N := by
  intro j
  by_cases hj : j ∈ S
  · simpa only [maskPartialSequence,ite_eq_left hj] using hv j
  · simp only [maskPartialSequence,ite_eq_right hj]
    exact N.zero_mem

theorem maskPartialSequence_orthogonal (S : Set ℕ) (v w : ℕ → PartialUnitary M)
    (hw : ∀ j ∈ S,(w j).support ≤ unitResidual (v j)) :
    ∀ j,(v j).support.val*(maskPartialSequence S w j).support.val=0 := by
  intro j
  by_cases hj : j ∈ S
  · simp only [maskPartialSequence,ite_eq_left hj]
    have hh := hw j hj
    change (1-(v j).support.val)*(w j).support.val=(w j).support.val at hh
    rw [sub_mul,one_mul] at hh
    exact sub_eq_self.mp hh
  · simp [maskPartialSequence,hj,zeroPartialUnitary]

def patchPartialSequence (v w : ℕ → PartialUnitary M)
    (h : ∀ j,(v j).support.val*(w j).support.val=0) : ℕ → PartialUnitary M :=
  fun j => ⟨⟨(v j).support.val+(w j).support.val,
    (v j).support.property.add (w j).support.property (h j)⟩,
      (v j).unitary.patch (w j).unitary (h j)⟩

theorem patchPartialSequence_bounded (v w : ℕ → PartialUnitary M)
    (h : ∀ j,(v j).support.val*(w j).support.val=0) :
    boundedPartialUnitary (patchPartialSequence v w h)=boundedPartialUnitary v+boundedPartialUnitary w ∧
    boundedPartialSupport (patchPartialSequence v w h)=boundedPartialSupport v+boundedPartialSupport w :=
  ⟨rfl,rfl⟩

theorem patchPartialSequence_mem (v w : ℕ → PartialUnitary M)
    (h : ∀ j,(v j).support.val*(w j).support.val=0)
    (hv : ∀ j,(v j).val.val ∈ N) (hw : ∀ j,(w j).val.val ∈ N) :
    ∀ j,(patchPartialSequence v w h j).val.val ∈ N :=
  fun j => N.add_mem (hv j) (hw j)

end

/-! An actual positive residual support increment with exact ordered moments
for arbitrary countably many centered compressed quotient coefficients. -/
open Filter
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

private theorem exists_supported_centered_contraction_family
    (g : Bounded M) (b : ℕ → Bounded M)
    (hl : ∀ i, g*b i=b i) (hr : ∀ i, b i*g=b i)
    (hc : ∀ i j, τ.trace ((b i).val j)=0) :
    ∃ (c : ℕ → ℂ) (a : ℕ → Bounded M),
      (∀ i, c i ≠ 0) ∧ (∀ i, g*a i=a i) ∧ (∀ i, a i*g=a i) ∧
      (∀ i j, ‖(a i).val j‖ ≤ 1) ∧ (∀ i j, τ.trace ((a i).val j)=0) ∧
      ∀ i, b i=c i • a i := by
  choose c hcne a hal har han hac hae using fun i =>
    exists_supported_centered_contraction (H := H) (M := M) τ g (b i) (hl i) (hr i) (hc i)
  exact ⟨c, a, hcne, hal, har, han, hac, hae⟩

variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ r : N.toStarSubalgebra,IsStarProjection r → r ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

private theorem residual_quotient_increment_of_normalized_representatives
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (v : ℕ → PartialUnitary M) (x : ℕ → Q τ ω)
    (g : Bounded M) (hg : ∀ j,IsStarProjection (g.val j))
    (hgN : ∀ j,(g.val j).val ∈ N) (hg0 : ∀ j,g.val j ≠ 0)
    (hgf : g.val =ᶠ[(ω : Filter ℕ)] (boundedPartialResidual v).val)
    (c : ℕ → ℂ) (a : ℕ → Bounded M)
    (han : ∀ i j, ‖(a i).val j‖ ≤ 1) (hac : ∀ i j,τ.trace ((a i).val j)=0)
    (hal : ∀ i,g*a i=a i) (har : ∀ i,a i*g=a i)
    (hscale : ∀ i,quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x i*
        quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)=
      c i • quotientMap τ (ω : Filter ℕ) (a i)) :
    ∃ w : ℕ → PartialUnitary M,
      (∀ j,(w j).val.val ∈ N) ∧
      (∀ j,(v j).support.val*(w j).support.val=0) ∧
      (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re/4 ≤
        (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialSupport w))).re ∧
      ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
        quotientTrace τ ω (
          optionalCoefficient (fun i => quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x i*
            quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)) first *
          algebraPatchingWord (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary w))
            (xs.map (fun a => (a.1,quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x a.2*
              quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))) ++
              [(s,optionalCoefficient (fun i => quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x i*
                quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)) last)]))=0 := by
  classical
  let f := boundedPartialResidual v
  obtain ⟨w,hwN,hws,hwt,hwm⟩ := exists_quotient_corner_partial_sequence (H := H) (N := N) (M := M) τ hNM hfactor hdiff hirr hsep
    ω hω g hg hgN hg0 a han hac hal har
  let S : Set ℕ := {j | g.val j=f.val j}
  have hS : S ∈ (ω : Filter ℕ) := hgf
  have he := maskPartialSequence_quotient τ (ω : Filter ℕ) S hS w
  have heg := quotientMap_eq_of_eventuallyEq τ (ω : Filter ℕ) g f hgf
  refine ⟨maskPartialSequence S w,maskPartialSequence_mem S w hwN,?_,?_,?_⟩
  · apply maskPartialSequence_orthogonal S v w
    intro j hj
    change f.val j*(w j).support.val=(w j).support.val
    exact (congrArg (fun q => q*(w j).support.val) hj.symm).trans (hws j)
  · exact (congrArg₂ (fun q r => (quotientTrace τ ω q).re/4 ≤
        (quotientTrace τ ω r).re) heg he.2.symm).mp hwt
  · intro first last xs s
    let F : Q τ ω → ℂ := fun u => quotientTrace τ ω (
      optionalCoefficient (fun i => quotientMap τ (ω : Filter ℕ) f*x i*
        quotientMap τ (ω : Filter ℕ) f) first *
      algebraPatchingWord u (xs.map (fun a => (a.1,quotientMap τ (ω : Filter ℕ) f*x a.2*
        quotientMap τ (ω : Filter ℕ) f)) ++ [(s,optionalCoefficient
          (fun i => quotientMap τ (ω : Filter ℕ) f*x i*quotientMap τ (ω : Filter ℕ) f) last)]))
    refine (congrArg F he.1).trans ?_
    exact (congrArg (quotientTrace τ ω)
      (ordered_moment_scale _ _ _ c hscale first last xs s)).trans
      ((trace_smul τ ω _ _).trans
        ((congrArg (fun z => _ * z) (hwm first last xs s)).trans (mul_zero _)))

private theorem residual_quotient_increment_of_representatives
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (v : ℕ → PartialUnitary M) (hv : ∀ j,(v j).val.val ∈ N)
    (x : ℕ → Q τ ω) (δ : ℝ) (hδ : 0 < δ) (g : Bounded M)
    (hg : ∀ j,IsStarProjection (g.val j)) (hgl : ∀ j,δ ≤ (τ.trace (g.val j)).re)
    (hgf : g.val =ᶠ[(ω : Filter ℕ)] (boundedPartialResidual v).val)
    (hgor : ∀ j,g.val j=(boundedPartialResidual v).val j ∨ g.val j=1)
    (b : ℕ → Bounded M) (hb : ∀ i,
      g*b i=b i ∧ b i*g=b i ∧ (∀ j,τ.trace ((b i).val j)=0) ∧
      quotientMap τ (ω : Filter ℕ) (b i)=
        quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x i*
          quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)) :
    ∃ w : ℕ → PartialUnitary M,
      (∀ j,(w j).val.val ∈ N) ∧
      (∀ j,(v j).support.val*(w j).support.val=0) ∧
      (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re/4 ≤
        (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialSupport w))).re ∧
      ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
        quotientTrace τ ω (
          optionalCoefficient (fun i => quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x i*
            quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)) first *
          algebraPatchingWord (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary w))
            (xs.map (fun a => (a.1,quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x a.2*
              quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))) ++
              [(s,optionalCoefficient (fun i => quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x i*
                quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)) last)]))=0 := by
  classical
  let f := boundedPartialResidual v
  have hgN : ∀ j,(g.val j).val ∈ N := by
    intro j
    rcases hgor j with h | h
    · rw [h]; exact boundedPartialResidual_mem v hv j
    · rw [h]; exact N.one_mem
  have hg0 : ∀ j,g.val j ≠ 0 := by
    intro j hz
    have hh := hgl j
    have hztrace : τ.trace (0 : M.toStarSubalgebra)=0 := inner_zero_right _
    rw [hz,hztrace,Complex.zero_re] at hh
    exact (not_le_of_gt hδ) hh
  obtain ⟨c,a,hcne,hal,har,han,hac,hae⟩ :=
    exists_supported_centered_contraction_family (H := H) (M := M) τ g b
      (fun i => (hb i).1) (fun i => (hb i).2.1) (fun i => (hb i).2.2.1)
  have hscale (i : ℕ) : quotientMap τ (ω : Filter ℕ) f*x i*quotientMap τ (ω : Filter ℕ) f=
      c i • quotientMap τ (ω : Filter ℕ) (a i) := by
    exact (hb i).2.2.2.symm.trans
      ((congrArg (quotientMap τ (ω : Filter ℕ)) (hae i)).trans
        (quotientMap_smul τ (ω : Filter ℕ) (c i) (a i)))
  exact residual_quotient_increment_of_normalized_representatives (H := H) (N := N) (M := M)
    τ hNM hfactor hdiff hirr hsep ω hω v x g hg hgN hg0 hgf c a han hac hal har hscale

theorem exists_residual_quotient_increment
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (v : ℕ → PartialUnitary M) (hv : ∀ j,(v j).val.val ∈ N)
    (ht : 0 < (quotientTrace τ ω
      (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re)
    (x : ℕ → Q τ ω)
    (hc : ∀ i,quotientTrace τ ω (
      quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x i*
      quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))=0) :
    ∃ w : ℕ → PartialUnitary M,
      (∀ j,(w j).val.val ∈ N) ∧
      (∀ j,(v j).support.val*(w j).support.val=0) ∧
      (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re/4 ≤
        (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialSupport w))).re ∧
      ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
        quotientTrace τ ω (
          optionalCoefficient (fun i => quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x i*
            quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)) first *
          algebraPatchingWord (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary w))
            (xs.map (fun a => (a.1,quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x a.2*
              quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))) ++
              [(s,optionalCoefficient (fun i => quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x i*
                quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)) last)]))=0 := by
  let f := boundedPartialResidual v
  obtain ⟨δ,hδ,g,hg,hgl,hgf,hgor,b,hb⟩ :=
    exists_eventually_centered_corner_representatives (H := H) (M := M) τ ω f
      (boundedPartialResidual_projection v) ht x hc
  exact residual_quotient_increment_of_representatives (H := H) (N := N) (M := M)
    τ hNM hfactor hdiff hirr hsep ω hω v hv x δ hδ g hg hgl hgf hgor b hb

end

/-! Faithful-trace completion criterion and the exact quarter-increment
residual estimate for actual orthogonal coordinate patches. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem quotient_projection_eq_zero_of_trace_re (p : Q τ ω) (hp : IsStarProjection p)
    (ht : (quotientTrace τ ω p).re=0) : p=0 := by
  have h : ‖p‖^2=0 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ),inner_eq_trace,hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]
    exact ht
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp h)

theorem quotient_unitary_of_zero_residual (v : ℕ → PartialUnitary M)
    (ht : (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re=0) :
    star (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v))*
      quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)=1 ∧
    quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)*
      star (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v))=1 := by
  have hp := ((boundedPartialSupport_projection v).one_sub).map (quotientStarAlgHom τ (ω : Filter ℕ))
  have hz := quotient_projection_eq_zero_of_trace_re τ ω _ hp ht
  change quotientMap τ (ω : Filter ℕ) (1-boundedPartialSupport v)=0 at hz
  rw [map_sub,map_one,sub_eq_zero] at hz
  constructor
  · rw [← quotientMap_star,← map_mul,boundedPartialUnitary_initial]
    exact hz.symm
  · rw [← quotientMap_star,← map_mul,boundedPartialUnitary_final]
    exact hz.symm

theorem quotient_patch_residual_bound (v w : ℕ → PartialUnitary M)
    (h : ∀ j,(v j).support.val*(w j).support.val=0)
    (ht : (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re/4 ≤
      (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialSupport w))).re) :
    (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ)
      (boundedPartialResidual (patchPartialSequence v w h)))).re ≤
      (3/4 : ℝ)*(quotientTrace τ ω
        (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re := by
  have he : boundedPartialResidual (patchPartialSequence v w h)=
      boundedPartialResidual v-boundedPartialSupport w := by
    unfold boundedPartialResidual
    rw [(patchPartialSequence_bounded v w h).2]
    abel
  have hsub : quotientTrace τ ω
      (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v) -
        quotientMap τ (ω : Filter ℕ) (boundedPartialSupport w)) =
      quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)) -
        quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialSupport w)) :=
    (traceLinear τ ω).map_sub
      (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))
      (quotientMap τ (ω : Filter ℕ) (boundedPartialSupport w))
  rw [he,map_sub,hsub,Complex.sub_re]
  linarith

end

/-! Actual moment-preserving residual extensions, retaining coordinate partial
unitaries in N and the quantitative decrease of residual support. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem bounded_orthogonal_patch_supported (v w : ℕ → PartialUnitary M)
    (h : ∀ j,(v j).support.val*(w j).support.val=0) :
    boundedPartialResidual v*boundedPartialUnitary w=boundedPartialUnitary w ∧
    boundedPartialUnitary w*boundedPartialResidual v=boundedPartialUnitary w := by
  have hl (j : ℕ) : (v j).support.val*(w j).val=0 := by
    calc (v j).support.val*(w j).val =
        (v j).support.val*((w j).support.val*(w j).val) := by rw [(w j).unitary.support_mul]
         _ = 0 := by rw [← mul_assoc,h j,zero_mul]
  have hr (j : ℕ) : (w j).val*(v j).support.val=0 := by
    have hqp : (w j).support.val*(v j).support.val=0 := by
      simpa only [star_mul,(v j).support.property.isSelfAdjoint.star_eq,
        (w j).support.property.isSelfAdjoint.star_eq,star_zero] using congrArg star (h j)
    calc (w j).val*(v j).support.val =
        ((w j).val*(w j).support.val)*(v j).support.val := by rw [(w j).unitary.mul_support]
         _ = 0 := by rw [mul_assoc,hqp,mul_zero]
  constructor
  · apply Subtype.ext
    funext j
    change (1-(v j).support.val)*(w j).val=(w j).val
    rw [sub_mul,one_mul,hl j,sub_zero]
  · apply Subtype.ext
    funext j
    change (w j).val*(1-(v j).support.val)=(w j).val
    rw [mul_sub,mul_one,hr j,sub_zero]

theorem quotient_orthogonal_patch_supported (ω : Ultrafilter ℕ)
    (v w : ℕ → PartialUnitary M) (h : ∀ j,(v j).support.val*(w j).support.val=0) :
    ∀ s,quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*
      algebraSignedLetter (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary w)) s=
      algebraSignedLetter (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary w)) s ∧
    algebraSignedLetter (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary w)) s*
      quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)=
      algebraSignedLetter (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary w)) s := by
  have hleft := congrArg (quotientMap τ (ω : Filter ℕ)) (bounded_orthogonal_patch_supported v w h).1
  have hright := congrArg (quotientMap τ (ω : Filter ℕ)) (bounded_orthogonal_patch_supported v w h).2
  rw [map_mul] at hleft hright
  have hf : star (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))=
      quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v) :=
    (((boundedPartialSupport_projection v).one_sub).map
      (quotientStarAlgHom τ (ω : Filter ℕ))).isSelfAdjoint.star_eq
  intro s
  cases s with
  | false => exact ⟨hleft,hright⟩
  | true =>
    constructor
    · simpa only [star_mul,hf,algebraSignedLetter,↓reduceIte] using congrArg star hright
    · simpa only [star_mul,hf,algebraSignedLetter,↓reduceIte] using congrArg star hleft

theorem patchPartialSequence_extends (v w : ℕ → PartialUnitary M)
    (h : ∀ j,(v j).support.val*(w j).support.val=0) :
    ∀ j,v j ≤ patchPartialSequence v w h j := by
  intro j
  change ((v j).unitary.patch (w j).unitary (h j)).val*(v j).support.val=(v j).val
  simpa only [(v j).unitary.initial] using
    (v j).unitary.patch_extends (w j).unitary (h j)

variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ r : N.toStarSubalgebra,IsStarProjection r → r ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

private theorem exact_residual_patch_of_centered_family (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (v : ℕ → PartialUnitary M) (hv : ∀ j,(v j).val.val ∈ N)
    (ht : 0 < (quotientTrace τ ω
      (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re)
    (x : ℕ → Q τ ω)
    (hm : ExactOrderedMoments τ ω
      (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)) x)
    (hz : ∀ i, let f := quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)
      let V := quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)
      quotientTrace τ ω (f*cyclicResidualFamily τ ω f (residualWordFamily τ ω V x) i*f)=0) :
    ∃ u : ℕ → PartialUnitary M,
      (∀ j,(u j).val.val ∈ N) ∧ (∀ j,v j ≤ u j) ∧
      ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u)) x ∧
      (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual u))).re ≤
        (3/4 : ℝ)*(quotientTrace τ ω
          (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re := by
  let V := quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)
  let f := quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)
  have hf : f*f=f :=
    (((boundedPartialSupport_projection v).one_sub).map
      (quotientStarAlgHom τ (ω : Filter ℕ))).isIdempotentElem.eq
  let y := residualWordFamily τ ω V x
  let z := cyclicResidualFamily τ ω f y
  obtain ⟨w,hwN,hortho,htrace,hmw⟩ := exists_residual_quotient_increment (H := H) (N := N) (M := M) τ hNM hfactor hdiff hirr hsep
    ω hω v hv ht z hz
  have hzs : (fun i => f*z i*f)=z := funext (cyclicResidualFamily_supported τ ω f hf y)
  have hwexact : ExactOrderedMoments τ ω
      (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary w)) z := by
    change ExactOrderedMoments τ ω _ (fun i => f*z i*f) at hmw
    rw [hzs] at hmw
    exact hmw
  refine ⟨patchPartialSequence v w hortho,patchPartialSequence_mem v w hortho hv hwN,
    patchPartialSequence_extends v w hortho,?_,quotient_patch_residual_bound τ ω v w hortho htrace⟩
  have he := (congrArg (quotientMap τ (ω : Filter ℕ))
    (patchPartialSequence_bounded v w hortho).1).trans
    (map_add (quotientMap τ (ω : Filter ℕ)) _ _)
  exact (congrArg (fun u => ExactOrderedMoments τ ω u x) he).mpr
    (exactOrderedMoments_add_of_cyclic τ ω V _ f x hm
      (quotient_orthogonal_patch_supported τ ω v w hortho) hwexact)

theorem exists_exact_residual_patch (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (v : ℕ → PartialUnitary M) (hv : ∀ j,(v j).val.val ∈ N)
    (ht : 0 < (quotientTrace τ ω
      (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re)
    (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0)
    (hm : ExactOrderedMoments τ ω
      (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)) x) :
    ∃ u : ℕ → PartialUnitary M,
      (∀ j,(u j).val.val ∈ N) ∧ (∀ j,v j ≤ u j) ∧
      ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u)) x ∧
      (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual u))).re ≤
        (3/4 : ℝ)*(quotientTrace τ ω
          (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re := by
  let V := quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)
  let P := quotientMap τ (ω : Filter ℕ) (boundedPartialSupport v)
  let f := quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)
  have hp : IsStarProjection P := (boundedPartialSupport_projection v).map
    (quotientStarAlgHom τ (ω : Filter ℕ))
  have hfp : f=1-P := by simp only [f,P,boundedPartialResidual,map_sub,map_one]
  have hf : f*f=f := by rw [hfp]; exact hp.one_sub.isIdempotentElem.eq
  have hi : star V*V=P := by
    dsimp only [V,P]
    rw [← quotientMap_star,← map_mul,boundedPartialUnitary_initial]
  have hfinal : V*star V=P := by
    dsimp only [V,P]
    rw [← quotientMap_star,← map_mul,boundedPartialUnitary_final]
  let y := residualWordFamily τ ω V x
  let z := cyclicResidualFamily τ ω f y
  have hy : ∀ i,quotientTrace τ ω (f*y i*f)=0 := by
    rw [hfp]
    exact residualWordFamily_compression_centered τ ω V P hp hi hfinal x hx hm
  have hnonzero : quotientTrace τ ω f ≠ 0 := by
    intro hz
    have hh : 0 < (quotientTrace τ ω f).re := ht
    rw [hz,Complex.zero_re] at hh
    exact lt_irrefl _ hh
  have hz : ∀ i,quotientTrace τ ω (f*z i*f)=0 :=
    cyclicResidualFamily_centered τ ω f hf hnonzero y hy
  exact exact_residual_patch_of_centered_family (H := H) (N := N) (M := M)
    τ hNM hfactor hdiff hirr hsep ω hω v hv ht x hm hz

end

/-! Iteration of actual moment-preserving partial-unitary extensions. Every
stage retains its coordinate representatives and a geometric residual bound. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def quotientResidualTrace (ω : Ultrafilter ℕ) (v : ℕ → PartialUnitary M) : ℝ :=
  (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re

theorem quotientResidualTrace_nonneg (ω : Ultrafilter ℕ) (v : ℕ → PartialUnitary M) :
    0 ≤ quotientResidualTrace τ ω v := by
  have hp := ((boundedPartialSupport_projection v).one_sub).map
    (quotientStarAlgHom τ (ω : Filter ℕ))
  change IsStarProjection (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)) at hp
  have hh := trace_square_nonneg τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))
  rwa [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq] at hh

variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ r : N.toStarSubalgebra,IsStarProjection r → r ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

theorem exists_exact_residual_step (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (v : ℕ → PartialUnitary M) (hv : ∀ j,(v j).val.val ∈ N)
    (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0)
    (hm : ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)) x) :
    ∃ u : ℕ → PartialUnitary M,
      (∀ j,(u j).val.val ∈ N) ∧ (∀ j,v j ≤ u j) ∧
      ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u)) x ∧
      quotientResidualTrace τ ω u ≤ (3/4 : ℝ)*quotientResidualTrace τ ω v := by
  by_cases ht : 0 < quotientResidualTrace τ ω v
  · exact exists_exact_residual_patch (H := H) (N := N) (M := M) τ hNM hfactor hdiff hirr hsep ω hω v hv ht x hx hm
  · have hz := le_antisymm (not_lt.mp ht) (quotientResidualTrace_nonneg τ ω v)
    exact ⟨v,hv,fun _ => le_rfl,hm,by rw [hz,mul_zero]⟩

theorem exists_exact_residual_iteration (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (v : ℕ → PartialUnitary M) (hv : ∀ j,(v j).val.val ∈ N)
    (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0)
    (hm : ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)) x) :
    ∃ a : ℕ → ℕ → PartialUnitary M,a 0=v ∧
      (∀ n j,(a n j).val.val ∈ N) ∧ (∀ j,Monotone (fun n => a n j)) ∧
      (∀ n,ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) x) ∧
      ∀ n,quotientResidualTrace τ ω (a n) ≤ (3/4 : ℝ)^n*quotientResidualTrace τ ω v := by
  let S := {u : ℕ → PartialUnitary M // (∀ j,(u j).val.val ∈ N) ∧
    ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u)) x}
  have next (u : S) : ∃ w : S,(∀ j,u.val j ≤ w.val j) ∧
      quotientResidualTrace τ ω w.val ≤ (3/4 : ℝ)*quotientResidualTrace τ ω u.val := by
    obtain ⟨w,hw,hle,hmw,hr⟩ := exists_exact_residual_step (H := H) (N := N) (M := M) τ hNM hfactor hdiff hirr hsep
      ω hω u.val u.property.1 x hx u.property.2
    exact ⟨⟨w,hw,hmw⟩,hle,hr⟩
  let step : S → S := fun u => (next u).choose
  have hs (u : S) := (next u).choose_spec
  let a : ℕ → S := fun n => Nat.rec (⟨v,hv,hm⟩ : S) (fun _ u => step u) n
  refine ⟨fun n => (a n).val,rfl,fun n => (a n).property.1,?_,fun n => (a n).property.2,?_⟩
  · intro j
    apply monotone_nat_of_le_succ
    intro n
    exact (hs (a n)).1 j
  · intro n
    induction n with
    | zero => simp only [pow_zero,one_mul]; exact le_rfl
    | succ n ih =>
      calc quotientResidualTrace τ ω (a (n+1)).val ≤
          (3/4 : ℝ)*quotientResidualTrace τ ω (a n).val := (hs (a n)).2
           _ ≤ (3/4 : ℝ)*((3/4 : ℝ)^n*quotientResidualTrace τ ω v) :=
             mul_le_mul_of_nonneg_left ih (by norm_num)
           _ = _ := by rw [pow_succ]; ring

end

/-! Coordinatewise monotone upper bounds and quantitative convergence in the
actual quotient two-norm. No completeness of the quotient is assumed. -/
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem quotient_trace_sub' (a b : Q τ ω) :
    quotientTrace τ ω (a-b)=quotientTrace τ ω a-quotientTrace τ ω b :=
  (traceLinear τ ω).map_sub a b

theorem quotientResidualTrace_eq (v : ℕ → PartialUnitary M) :
    quotientResidualTrace τ ω v =
      1-(quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialSupport v))).re := by
  simp only [quotientResidualTrace,boundedPartialResidual,map_sub,map_one,
    quotient_trace_sub',quotientTrace_one,Complex.sub_re,Complex.one_re]

theorem quotient_partial_distance_sq (v w : ℕ → PartialUnitary M) (h : ∀ j,v j ≤ w j) :
    ‖quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary w)-
      quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)‖^2=
      quotientResidualTrace τ ω v-quotientResidualTrace τ ω w := by
  have he : star (boundedPartialUnitary w-boundedPartialUnitary v)*
      (boundedPartialUnitary w-boundedPartialUnitary v)=boundedPartialSupport w-boundedPartialSupport v := by
    apply Subtype.ext
    funext j
    exact PartialUnitary.difference_square (h j)
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),inner_eq_trace,← map_sub,← quotientMap_star,← map_mul,he,
    map_sub,quotient_trace_sub']
  change (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialSupport w))-
    quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialSupport v))).re = _
  rw [Complex.sub_re,quotientResidualTrace_eq,quotientResidualTrace_eq]
  ring

theorem quotientResidualTrace_antitone (v w : ℕ → PartialUnitary M) (h : ∀ j,v j ≤ w j) :
    quotientResidualTrace τ ω w ≤ quotientResidualTrace τ ω v := by
  have he := quotient_partial_distance_sq τ ω v w h
  nlinarith [sq_nonneg ‖quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary w)-
    quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)‖]

include τ in
theorem exists_coordinate_monotone_upper (hNM : N ≤ M)
    (a : ℕ → ℕ → PartialUnitary M) (ha : ∀ j,Monotone (fun n => a n j))
    (hN : ∀ n j,(a n j).val.val ∈ N) :
    ∃ u : ℕ → PartialUnitary M,(∀ j,(u j).val.val ∈ N) ∧ ∀ n j,a n j ≤ u j := by
  choose u hu hlim using fun j => PartialUnitary.monotone_limit τ (fun n => a n j) (ha j)
  refine ⟨u,fun j => ?_,fun n j => hu j n⟩
  exact inclusion_mem_of_bounded_L2_limit τ hNM (fun n => (a n j).val) (u j).val
    1 zero_le_one (fun n => (a n j).unitary.norm_le_one) (fun n => hN n j) (hlim j)

theorem quotient_geometric_upper_completion
    (a : ℕ → ℕ → PartialUnitary M) (u : ℕ → PartialUnitary M)
    (hu : ∀ n j,a n j ≤ u j) (r : ℝ)
    (hr : ∀ n,quotientResidualTrace τ ω (a n) ≤ (3/4 : ℝ)^n*r) :
    quotientResidualTrace τ ω u=0 ∧
    Tendsto (fun n => quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) atTop
      (𝓝 (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u))) := by
  have ht : Tendsto (fun n : ℕ => (3/4 : ℝ)^n*r) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3/4) (by norm_num : (3/4 : ℝ) < 1)).mul_const r
  have hz : quotientResidualTrace τ ω u=0 := by
    apply le_antisymm _ (quotientResidualTrace_nonneg τ ω u)
    apply ge_of_tendsto ht
    exact Eventually.of_forall (fun n =>
      (quotientResidualTrace_antitone τ ω (a n) u (hu n)).trans (hr n))
  refine ⟨hz,?_⟩
  have hs : Tendsto (fun n => ‖quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u)-
      quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))‖^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _) _ ht
    intro n
    rw [quotient_partial_distance_sq τ ω (a n) u (hu n),hz,sub_zero]
    exact hr n
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hn : Tendsto (fun n => ‖quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u)-
      quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hs.sqrt
  exact hn.congr (fun n => norm_sub_rev _ _)

end Generator.Tracial

end

end OAI
