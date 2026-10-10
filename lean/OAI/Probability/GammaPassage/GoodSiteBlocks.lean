import OAI.Probability.GammaPassage.HighDensityOriented
import OAI.Probability.GammaPassage.RareFastEvents

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

def blockLayer (v : Vertex) : ℤ := v.1+v.2

def blockLevel (v : Vertex) : ℤ := v.1+2*v.2

def blockX (n d : ℤ) (v : Vertex) : ℤ := blockLayer v*(n+d)

noncomputable def blockY (σ S : ℝ) (v : Vertex) : ℝ := σ*(blockLevel v : ℝ)*S

noncomputable def blockRegion (b A : ℝ) (n d : ℤ) (σ S : ℝ) (v : Vertex) : Set Vertex :=
  {p | |(p.1 : ℝ)-(blockX n d v : ℝ)| ≤ (A+3)*n ∧
    |transverse b p-blockY σ S v| ≤ 4*S}

theorem centers_close_of_point (a b t R : ℝ)
    (ha : |t-a| ≤ R) (hb : |t-b| ≤ R) : |a-b| ≤ 2*R := by
  have hh := abs_sub_le (t-b) 0 (t-a)
  simp only [sub_zero, zero_sub, abs_neg] at hh
  have he : (t-b)-(t-a)=a-b := by ring
  rw [he] at hh
  linarith

/-- Sharing one support vertex bounds both transformed lattice indices.
Crucially these bounds contain neither M nor D0. -/
theorem blockRegion_common_indices (b A : ℝ) (n d : ℤ) (σ S : ℝ)
    (hn : 0 < n) (hd : 0 ≤ d) (hσ : |σ|=1) (hS : 0 < S)
    (v w p : Vertex) (hv : p ∈ blockRegion b A n d σ S v)
    (hw : p ∈ blockRegion b A n d σ S w) :
    |((blockLayer v-blockLayer w : ℤ) : ℝ)| ≤ 2*(A+3) ∧
    |((blockLevel v-blockLevel w : ℤ) : ℝ)| ≤ 8 := by
  have hx := centers_close_of_point _ _ _ _ hv.1 hw.1
  have hy := centers_close_of_point _ _ _ _ hv.2 hw.2
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd
  have hxx : |(blockX n d v : ℝ)-(blockX n d w : ℝ)| =
      |((blockLayer v-blockLayer w : ℤ) : ℝ)| *((n : ℝ)+d) := by
    simp only [blockX, Int.cast_mul, Int.cast_add, Int.cast_sub]
    rw [← sub_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)+d)]
  have hyy : |blockY σ S v-blockY σ S w| =
      |((blockLevel v-blockLevel w : ℤ) : ℝ)| *S := by
    have he : blockY σ S v-blockY σ S w =
        σ*((blockLevel v : ℝ)-(blockLevel w : ℝ))*S := by unfold blockY; ring
    rw [he,abs_mul,abs_mul,hσ,one_mul,abs_of_pos hS,Int.cast_sub]
  rw [hxx] at hx
  rw [hyy] at hy
  constructor
  · nlinarith [mul_nonneg (abs_nonneg (((blockLayer v-blockLayer w : ℤ) : ℝ))) hd']
  · nlinarith

theorem blockRegion_common_near (b A : ℝ) (n d : ℤ) (σ S : ℝ) (k : ℕ)
    (hn : 0 < n) (hd : 0 ≤ d) (hσ : |σ|=1) (hS : 0 < S)
    (hA : 0 ≤ A+3) (hk : 4*(A+3)+8 ≤ k)
    (v w p : Vertex) (hv : p ∈ blockRegion b A n d σ S v)
    (hw : p ∈ blockRegion b A n d σ S w) : latticeNear k v w := by
  obtain ⟨hi,hj⟩ := blockRegion_common_indices b A n d σ S hn hd hσ hS v w p hv hw
  have he1 : ((v.1-w.1 : ℤ) : ℝ) =
      2*((blockLayer v-blockLayer w : ℤ) : ℝ)-((blockLevel v-blockLevel w : ℤ) : ℝ) := by
    simp [blockLayer,blockLevel]; ring
  have he2 : ((v.2-w.2 : ℤ) : ℝ) =
      ((blockLevel v-blockLevel w : ℤ) : ℝ)-((blockLayer v-blockLayer w : ℤ) : ℝ) := by
    simp [blockLayer,blockLevel]; ring
  have hx : |((v.1-w.1 : ℤ) : ℝ)| ≤ k := by
    rw [he1]
    have hh := abs_sub_le (2*((blockLayer v-blockLayer w : ℤ) : ℝ)) 0
      (((blockLevel v-blockLevel w : ℤ) : ℝ))
    simp only [sub_zero, zero_sub, abs_neg] at hh
    rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)] at hh
    linarith
  have hy : |((v.2-w.2 : ℤ) : ℝ)| ≤ k := by
    rw [he2]
    have hh := abs_sub_le (((blockLevel v-blockLevel w : ℤ) : ℝ)) 0
      (((blockLayer v-blockLayer w : ℤ) : ℝ))
    simp only [sub_zero, zero_sub, abs_neg] at hh
    linarith
  have hx' : -(k : ℤ) ≤ v.1-w.1 ∧ v.1-w.1 ≤ k := by
    constructor
    · exact_mod_cast (abs_le.mp hx).1
    · exact_mod_cast (abs_le.mp hx).2
  have hy' : -(k : ℤ) ≤ v.2-w.2 ∧ v.2-w.2 ≤ k := by
    constructor
    · exact_mod_cast (abs_le.mp hy).1
    · exact_mod_cast (abs_le.mp hy).2
  dsimp [latticeNear]
  omega

/-- A radius uniform in the connector gap works at every positive scale. -/
theorem blockRegion_disjoint (b A : ℝ) (n d : ℤ) (σ S : ℝ)
    (hn : 0 < n) (hd : 0 ≤ d) (hσ : |σ|=1) (hS : 0 < S) (hA : 0 < A)
    (v w : Vertex) (hvw : ¬latticeNear (⌈4*(A+3)+8⌉₊+1) v w) :
    Disjoint (blockRegion b A n d σ S v) (blockRegion b A n d σ S w) := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  apply hvw
  apply blockRegion_common_near b A n d σ S _ hn hd hσ hS (by linarith) _ v w p hp hq
  have hh := Nat.le_ceil (4*(A+3)+8)
  push_cast
  linarith

theorem blockRegion_finite (b A : ℝ) (n d : ℤ) (σ S : ℝ) (v : Vertex) :
    (blockRegion b A n d σ S v).Finite :=
  finite_tilted_rectangle b (blockX n d v) (blockY σ S v) ((A+3)*n) (4*S)

noncomputable def blockVertices (b A : ℝ) (n d : ℤ) (σ S : ℝ) (v : Vertex) : Finset Vertex :=
  (blockRegion_finite b A n d σ S v).toFinset

@[simp] theorem mem_blockVertices (b A : ℝ) (n d : ℤ) (σ S : ℝ) (v p : Vertex) :
    p ∈ blockVertices b A n d σ S v ↔ p ∈ blockRegion b A n d σ S v :=
  (blockRegion_finite b A n d σ S v).mem_toFinset

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- Tests supported on sufficiently separated finite block regions are
jointly independent, as required by Lemma `cr:oriented-paths`. -/
theorem block_supported_tests_independent (h : GammaEnvironment shape rate P τ)
    (b A : ℝ) (n d : ℤ) (σ S : ℝ)
    (hn : 0 < n) (hd : 0 ≤ d) (hσ : |σ|=1) (hS : 0 < S) (hA : 0 < A)
    (E : Vertex → Set (Edge → ℝ)) (hE : ∀ v, MeasurableSet (E v))
    (hsupport : ∀ v, DependsOnEdges (E v) (internalEdges (blockVertices b A n d σ S v))) :
    SeparatedGoodIndependent P (fun v => {ω | (fun e => τ e ω) ∈ E v})
      (⌈4*(A+3)+8⌉₊+1) := by
  intro T hT
  apply Grid.disjoint_edge_events_iIndepSet h (fun v : T => E v.val)
    (fun v : T => internalEdges (blockVertices b A n d σ S v.val))
    (fun v => hE v.val) (fun v => hsupport v.val)
  intro v w hvw
  apply internalEdges_disjoint
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hsep := hT v.property w.property (fun hh => hvw (Subtype.ext hh))
  exact Set.disjoint_left.mp (blockRegion_disjoint b A n d σ S hn hd hσ hS hA v.val w.val hsep)
    ((mem_blockVertices ..).mp hp) ((mem_blockVertices ..).mp hq)

end GammaFPP.CrossingBridge

end OAI
