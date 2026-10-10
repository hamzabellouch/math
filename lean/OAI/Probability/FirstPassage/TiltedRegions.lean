import OAI.Probability.FirstPassage.RareFastGeometry

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

theorem finite_tilted_rectangle (b X Y L H : ℝ) :
    {p : Vertex | |(p.1 : ℝ)-X| ≤ L ∧ |transverse b p-Y| ≤ H}.Finite := by
  let B := |X|+|L|+|Y|+|H|+|b| *(|X|+|L|)
  obtain ⟨N,hN⟩ := exists_nat_gt B
  apply (Finset.finite_toSet (latticeBox N)).subset
  intro p hp
  obtain ⟨hpL,hpH⟩ := hp
  have hx : |(p.1 : ℝ)| ≤ |X|+|L| := by
    have hh := abs_add_le ((p.1 : ℝ)-X) X
    rw [sub_add_cancel] at hh
    linarith [le_abs_self L]
  have hy : |(p.2 : ℝ)| ≤ |Y|+|H|+|b| *(|X|+|L|) := by
    have hh := abs_add_le (transverse b p-Y) (Y+b*(p.1 : ℝ))
    have heq : transverse b p-Y+(Y+b*(p.1 : ℝ))=(p.2 : ℝ) := by unfold transverse; ring
    rw [heq] at hh
    have hh' := abs_add_le Y (b*(p.1 : ℝ))
    rw [abs_mul] at hh'
    have ht := mul_le_mul_of_nonneg_left hx (abs_nonneg b)
    linarith [le_abs_self H]
  have hxB : |(p.1 : ℝ)| < N := by
    dsimp [B] at hN
    nlinarith [abs_nonneg Y,abs_nonneg H,mul_nonneg (abs_nonneg b) (add_nonneg (abs_nonneg X) (abs_nonneg L))]
  have hyB : |(p.2 : ℝ)| < N := by
    dsimp [B] at hN
    linarith [abs_nonneg X,abs_nonneg L]
  have hx' : -(N : ℤ) ≤ p.1 ∧ p.1 ≤ N := by
    constructor
    · exact_mod_cast (abs_le.mp hxB.le).1
    · exact_mod_cast (abs_le.mp hxB.le).2
  have hy' : -(N : ℤ) ≤ p.2 ∧ p.2 ≤ N := by
    constructor
    · exact_mod_cast (abs_le.mp hyB.le).1
    · exact_mod_cast (abs_le.mp hyB.le).2
  change p ∈ latticeBox N
  simpa only [latticeBox,Finset.mem_product,Finset.mem_Icc] using And.intro hx' hy'

theorem blockRegion_finite (b A : ℝ) (n d : ℤ) (σ S : ℝ) (v : Vertex) :
    (blockRegion b A n d σ S v).Finite :=
  finite_tilted_rectangle b (blockX n d v) (blockY σ S v) ((A+3)*n) (4*S)

noncomputable def blockVertices (b A : ℝ) (n d : ℤ) (σ S : ℝ) (v : Vertex) : Finset Vertex :=
  (blockRegion_finite b A n d σ S v).toFinset

@[simp] theorem mem_blockVertices (b A : ℝ) (n d : ℤ) (σ S : ℝ) (v p : Vertex) :
    p ∈ blockVertices b A n d σ S v ↔ p ∈ blockRegion b A n d σ S v :=
  (blockRegion_finite b A n d σ S v).mem_toFinset

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem block_supported_tests_independent (h : ExponentialEnvironment P τ)
    (b A : ℝ) (n d : ℤ) (σ S : ℝ)
    (hn : 0 < n) (hd : 0 ≤ d) (hσ : |σ|=1) (hS : 0 < S) (hA : 0 < A)
    (E : Vertex → Set (Edge → ℝ)) (hE : ∀ v, MeasurableSet (E v))
    (hsupport : ∀ v, DependsOnEdges (E v) (internalEdges (blockVertices b A n d σ S v))) :
    SeparatedGoodIndependent P (fun v => {ω | (fun e => τ e ω) ∈ E v})
      (⌈4*(A+3)+8⌉₊+1) := by
  intro T hT
  apply disjoint_edge_events_iIndepSet h (fun v : T => E v.val)
    (fun v : T => internalEdges (blockVertices b A n d σ S v.val))
    (fun v => hE v.val) (fun v => hsupport v.val)
  intro v w hvw
  apply internalEdges_disjoint
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hsep := hT v.property w.property (fun hh => hvw (Subtype.ext hh))
  exact Set.disjoint_left.mp (blockRegion_disjoint b A n d σ S hn hd hσ hS hA v.val w.val hsep)
    ((mem_blockVertices ..).mp hp) ((mem_blockVertices ..).mp hq)

end PlanarFPP

end OAI
