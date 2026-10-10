import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialWordIsometry
import OAI.Analysis.KadisonSimilarity.Representation.ClosedFamilySpan

namespace OAI

/-! Centered leading-word subspaces for the creation operators. Density of
all centered words follows by centering the two unrestricted endpoints. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)

def centeredFreeWordVectors : Set H := {v | ∃ (side : Bool) (xs : List P),
  AlternatingCenteredWord G.trace A D side xs ∧ v = G.vector xs.prod}

def centeredFreeWordSpan : Submodule ℂ H :=
  Submodule.span ℂ (centeredFreeWordVectors G A D)

theorem centered_word_mem_span {side : Bool} {xs : List P}
    (hxs : AlternatingCenteredWord G.trace A D side xs) :
    G.vector xs.prod ∈ centeredFreeWordSpan G A D :=
  Submodule.subset_span ⟨side, xs, hxs, rfl⟩

theorem full_pairWord_mem_span (hτ : G.trace 1 = 1) {xs : List P}
    (hxs : CenteredPairWord G.trace A D xs) (d : D) (b : A) :
    G.vector ((d : P) * xs.prod * (b : P)) ∈ centeredFreeWordSpan G A D := by
  let d₀ := traceCentered G.trace (d : P)
  let b₀ := traceCentered G.trace (b : P)
  have hd := traceCentered_mem G.trace D d.property
  have hb := traceCentered_mem G.trace A b.property
  have hd0 := traceCentered_trace G.trace hτ (d : P)
  have hb0 := traceCentered_trace G.trace hτ (b : P)
  have h1 : G.vector (d₀ * xs.prod * b₀) ∈ centeredFreeWordSpan G A D := by
    have hx := centered_word_mem_span G A D
      (AlternatingCenteredWord.cons (side := false) hd hd0 (hxs.alternating_append hb hb0))
    simpa only [List.prod_cons, List.prod_append, List.prod_singleton,
      List.prod_nil, mul_one, mul_assoc] using hx
  have h2 : G.vector (d₀ * xs.prod) ∈ centeredFreeWordSpan G A D := by
    exact centered_word_mem_span G A D (.cons (side := false) hd hd0 hxs.alternating)
  have h3 : G.vector (xs.prod * b₀) ∈ centeredFreeWordSpan G A D := by
    simpa only [List.prod_append, List.prod_singleton] using
      centered_word_mem_span G A D (hxs.alternating_append hb hb0)
  have h4 := centered_word_mem_span G A D hxs.alternating
  have he : (d : P) * xs.prod * (b : P) =
      d₀ * xs.prod * b₀ + G.trace (b : P) • (d₀ * xs.prod) +
        G.trace (d : P) • (xs.prod * b₀) +
          (G.trace (d : P) * G.trace (b : P)) • xs.prod := by
    calc
      _ = (d₀ + G.trace (d : P) • 1) * xs.prod *
          (b₀ + G.trace (b : P) • 1) := by
        dsimp [d₀, b₀]
        rw [traceCentered_add, traceCentered_add]
      _ = _ := by
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul,
          mul_one, smul_add, smul_smul, mul_comm (G.trace (b : P)) (G.trace (d : P))]
        abel
  rw [he, map_add, map_add, map_add, map_smul, map_smul, map_smul]
  exact (centeredFreeWordSpan G A D).add_mem
    ((centeredFreeWordSpan G A D).add_mem
      ((centeredFreeWordSpan G A D).add_mem h1
        ((centeredFreeWordSpan G A D).smul_mem _ h2))
      ((centeredFreeWordSpan G A D).smul_mem _ h3))
    ((centeredFreeWordSpan G A D).smul_mem _ h4)

theorem centeredFreeWordSpan_dense (hτ : G.trace 1 = 1)
    (hgen : ReducedWordGenerated G A D) :
    (centeredFreeWordSpan G A D).topologicalClosure = ⊤ := by
  apply top_unique
  rw [← hgen]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨n, d, b, a, c, ha, hc, rfl⟩
  change G.vector ((d : P) * alternatingProduct (fun i => (a i : P))
    (fun i => (c i : P)) * (b : P)) ∈ centeredFreeWordSpan G A D
  have hp := CenteredPairWord.of_pairWord (τ := G.trace)
    (fun i => (a i : P)) (fun i => (c i : P))
    (fun i => (a i).property) (fun i => (c i).property) ha hc
  simpa only [prod_pairWord, alternatingProduct] using full_pairWord_mem_span G A D hτ hp d b

abbrev CenteredWordParameter (side : Bool) :=
  {xs : List P // AlternatingCenteredWord G.trace A D side xs}

abbrev LeadingWordParameter (side : Bool) :=
  {xs : CenteredWordParameter G A D side // xs.1 ≠ []}

def centeredWordFamily (side : Bool) (xs : CenteredWordParameter G A D side) : H :=
  G.vector xs.1.prod

def leadingWordFamily (side : Bool) (xs : LeadingWordParameter G A D side) : H :=
  G.vector xs.1.1.prod

abbrev centeredWordSpace (side : Bool) : ClosedSubmodule ℂ H :=
  closedFamilySpan (centeredWordFamily G A D side)

abbrev leadingWordSpace (side : Bool) : ClosedSubmodule ℂ H :=
  closedFamilySpan (leadingWordFamily G A D side)

theorem inner_leading_opposite_word (hf : ScalarFree G.trace A D)
    (side : Bool) (xs : LeadingWordParameter G A D side)
    (ys : CenteredWordParameter G A D (!side)) :
    inner ℂ (leadingWordFamily G A D side xs) (centeredWordFamily G A D (!side) ys) = 0 := by
  rw [leadingWordFamily, centeredWordFamily, G.inner_vector]
  exact hf.trace_opposite_words G.trace_star xs.1.2 ys.2 (Or.inl xs.2)

theorem inner_leading_opposite_space (hf : ScalarFree G.trace A D) (side : Bool)
    (x : leadingWordSpace G A D side) (y : centeredWordSpace G A D (!side)) :
    inner ℂ (x : H) (y : H) = 0 :=
  closedFamilySpan_inner_zero (leadingWordFamily G A D side)
    (centeredWordFamily G A D (!side)) (inner_leading_opposite_word G A D hf side) x y

theorem vacuum_mem_centeredWordSpace (side : Bool) :
    G.vector 1 ∈ centeredWordSpace G A D side := by
  have h := (closedFamilyVector (centeredWordFamily G A D side)
    ⟨[], .nil side⟩).property
  exact h

theorem leadingWordSpace_le_centeredWordSpace (side : Bool) :
    (leadingWordSpace G A D side).toSubmodule ≤ (centeredWordSpace G A D side).toSubmodule := by
  apply closedFamilySpan_le
  intro xs
  exact (closedFamilyVector (centeredWordFamily G A D side) xs.1).property

def leadingIntoCentered (side : Bool) :
    leadingWordSpace G A D side →ₗᵢ[ℂ] centeredWordSpace G A D side where
  toLinearMap := Submodule.inclusion (leadingWordSpace_le_centeredWordSpace G A D side)
  norm_map' _ := rfl

@[simp] theorem leadingIntoCentered_coe (side : Bool) (x : leadingWordSpace G A D side) :
    (leadingIntoCentered G A D side x : H) = x := rfl

end KadisonSimilarity

end

end OAI
