import Mathlib
import OAI.GroupTheory.SimpleAmenable.Amenability.BarrierLineGeometry

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section BarrierAlgorithm
open Classical Set

noncomputable def barrierSitePoint {a m D : ℕ} {v : ℝ×ℝ} (z : FlagSite a m D v) : ℝ×ℝ :=
  z.val.2.val

theorem flagSite_eq_of_track_point {a m D : ℕ} {v : ℝ×ℝ}
    {z w : FlagSite a m D v} (ht : z.val.1=w.val.1)
    (hp : barrierSitePoint z=barrierSitePoint w) : z=w := by
  apply Subtype.ext
  exact Prod.ext ht (Subtype.ext hp)

noncomputable def barrierMarkedParameters {a m : ℕ} (ha : 0<a) (i : Fin m)
    (j : Fin 4) (c : CutRing)
    (M : Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j))) : Finset ℝ :=
  (M.filter (fun z => z.val.1=i ∧ barrierSitePoint z∈squareInterior ∧
    cutForm a j (barrierSitePoint z)=ordinary c)).image
      (fun z => barrierLineParameter j (barrierSitePoint z))

noncomputable def barrierSubdivision {a m : ℕ} (ha : 0<a) (i : Fin m)
    (j : Fin 4) (c : CutRing)
    (M : Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j))) : Finset ℝ :=
  {barrierLineLower a j c,barrierLineUpper a j c} ∪ barrierMarkedParameters ha i j c M

noncomputable def barrierActivation {a m : ℕ} (ha : 0<a) (i : Fin m)
    (j : Fin 4) (c : CutRing)
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (s : ℝ) : Bool := decide (∃z,z.val.1=i ∧
      barrierSitePoint z=barrierLinePoint a j c s ∧ b z=true)

def ConsecutiveSubdivision (E : Finset ℝ) (s t : ℝ) : Prop :=
  s∈E ∧ t∈E ∧ s<t ∧ ∀r∈E,s<r → t≤r

noncomputable def barrierActiveIntervals {a m : ℕ} (ha : 0<a) (i : Fin m)
    (j : Fin 4) (c : CutRing)
    (M : Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool) :
    Finset (ℝ×ℝ) :=
  ((barrierSubdivision ha i j c M) ×ˢ (barrierSubdivision ha i j c M)).filter
    (fun st => ConsecutiveSubdivision (barrierSubdivision ha i j c M) st.1 st.2 ∧
      barrierActivation ha i j c b st.1=true)

theorem barrierActivation_at_site {a m : ℕ} (ha : 0<a) (i : Fin m)
    (j : Fin 4) (c : CutRing)
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (s : ℝ) (z : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j))
    (ht : z.val.1=i) (hp : barrierSitePoint z=barrierLinePoint a j c s) :
    barrierActivation ha i j c b s=b z := by
  apply Bool.eq_iff_iff.mpr
  simp only [barrierActivation,decide_eq_true_eq]
  constructor
  · rintro ⟨w,hw,hwp,hb⟩
    have he : w=z := flagSite_eq_of_track_point (hw.trans ht.symm) (hwp.trans hp.symm)
    simpa [he] using hb
  · intro hb
    exact ⟨z,ht,hp,hb⟩

theorem mem_barrierSubdivision_bounds {a m : ℕ} (ha : 0<a) (i : Fin m)
    {j : Fin 4} {N : ℝ} {c : CutRing} (hc : c∈barrierCandidate a j N)
    (M : Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    {s : ℝ} (hs : s∈barrierSubdivision ha i j c M) :
    s∈Icc (barrierLineLower a j c) (barrierLineUpper a j c) := by
  have hgap := (barrierLineLower_lt_upper hc).le
  simp only [barrierSubdivision,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with (rfl | rfl) | hs
  · exact ⟨le_rfl,hgap⟩
  · exact ⟨hgap,le_rfl⟩
  · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨_,hzt,hzp,hzc⟩ := Finset.mem_filter.mp hz
    have hp : barrierLinePoint a j c (barrierLineParameter j (barrierSitePoint z))∈squareInterior := by
      rwa [barrierLinePoint_parameter hzc]
    exact ⟨((barrierLinePoint_interior_iff hc _).mp hp).1.le,
      ((barrierLinePoint_interior_iff hc _).mp hp).2.le⟩

theorem barrierSubdivision_start_site {a m : ℕ} (ha : 0<a) (i : Fin m)
    {j : Fin 4} {N : ℝ} {c : CutRing} (hc : c∈barrierCandidate a j N)
    (M : Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    {s t : ℝ} (h : ConsecutiveSubdivision (barrierSubdivision ha i j c M) s t) :
    ∃z : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j),
      z.val.1=i ∧ barrierSitePoint z=barrierLinePoint a j c s ∧
      (s=barrierLineLower a j c ∨ z∈M) := by
  have hs := h.1
  have ht := mem_barrierSubdivision_bounds ha i hc M h.2.1
  simp only [barrierSubdivision,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with (rfl | rfl) | hs
  · exact ⟨barrierIncomingSite ha i hc,rfl,rfl,Or.inl rfl⟩
  · exact False.elim (not_lt_of_ge ht.2 h.2.2.1)
  · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hzM,hzt,hzp,hzc⟩ := Finset.mem_filter.mp hz
    exact ⟨z,hzt,(barrierLinePoint_parameter hzc).symm,Or.inr hzM⟩

def BarrierLineIndex (a : ℕ) (N : ℝ) := Σj : Fin 4,{c : CutRing // c∈barrierCandidate a j N}

@[instance_reducible] noncomputable def barrierLineIndexFintype (a : ℕ) {N : ℝ} (hN : 0<N) :
    Fintype (BarrierLineIndex a N) := by
  letI (j : Fin 4) : Fintype {c : CutRing // c∈barrierCandidate a j N} :=
    (barrierCandidate_finite a j hN).fintype
  exact inferInstanceAs (Fintype (Σj : Fin 4,{c : CutRing // c∈barrierCandidate a j N}))

noncomputable def sampledBarriers {a m : ℕ} (ha : 0<a) (i : Fin m) (N : ℝ)
    (M : ∀j,Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    (b : ∀j,FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool) :
    Set (ℝ×ℝ) :=
  {p | ∃l : BarrierLineIndex a N,∃st∈barrierActiveIntervals ha i l.1 l.2.val (M l.1) (b l.1),
    p∈barrierLinePoint a l.1 l.2.val '' Icc st.1 st.2}

theorem sampledBarriers_supported {a m : ℕ} (ha : 0<a) (i : Fin m) (N : ℝ)
    (M : ∀j,Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    (b : ∀j,FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool) :
    SupportedBarriers a (fun l : BarrierLineIndex a N => l.1) (fun l => l.2.val)
      (sampledBarriers ha i N M b) := by
  rintro p ⟨l,st,hst,t,ht,rfl⟩
  exact ⟨l,cutForm_barrierLinePoint a l.1 l.2.val t⟩

noncomputable def sampledPolygonPartition {a m : ℕ} (ha : 0<a) (i : Fin m)
    {N : ℝ} (hN : 0<N)
    (M : ∀j,Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    (b : ∀j,FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool) :
    FinitePolygonPartition a := by
  letI := barrierLineIndexFintype a hN
  exact finiteBarrierPartition (sampledBarriers_supported ha i N M b)

theorem barrierLinePoint_continuous (a : ℕ) (j : Fin 4) (c : CutRing) :
    Continuous (barrierLinePoint a j c) := by
  change Continuous (fun t => barrierLinePoint a j c t)
  fin_cases j <;> simp only [barrierLinePoint] <;> fun_prop

theorem sampledBarriers_closed {a m : ℕ} (ha : 0<a) (i : Fin m) {N : ℝ} (hN : 0<N)
    (M : ∀j,Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    (b : ∀j,FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool) :
    IsClosed (sampledBarriers ha i N M b) := by
  let := barrierLineIndexFintype a hN
  have he : sampledBarriers ha i N M b=⋃l : BarrierLineIndex a N,
      ⋃st∈barrierActiveIntervals ha i l.1 l.2.val (M l.1) (b l.1),
        barrierLinePoint a l.1 l.2.val '' Icc st.1 st.2 := by
    ext p; simp [sampledBarriers]
  rw [he]
  apply isClosed_iUnion_of_finite
  intro l
  apply isClosed_biUnion_finset
  intro st hst
  exact (isCompact_Icc.image (barrierLinePoint_continuous a l.1 l.2.val)).isClosed

end BarrierAlgorithm

end SimpleAmenable
end
end

end OAI
