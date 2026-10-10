import OAI.Geometry.ComplexBundle.Avoidance
import Mathlib.LinearAlgebra.Dimension.RankNullity

namespace OAI

noncomputable section

/-! Finite-point incidence avoidance and expansion inequalities. -/

section
open scoped MeasureTheory
open Set Module MeasureTheory MeasureTheory.Measure
namespace Kaplansky.Incidence
open ComplexGrassmann
variable {q s k t l : ℕ}

def PointBad : Set (TupleOperators q s k t l) :=
  {T | ∃ (P : Grassmann s k) (Q : Grassmann t l), ∀ i, ∀ x ∈ P.val, T i x ∈ Q.val}

/-- The full bad locus over a point is null, across ALL s-planes and t-planes.
The countable graph cover is constructed from the actual Grassmann spaces. -/
theorem pointBad_null [MeasurableSpace (TupleOperators q s k t l)]
    [BorelSpace (TupleOperators q s k t l)] (hgap : s*k+t*l<q*s*l) :
    μH[finrank ℝ (TupleOperators q s k t l)] (PointBad (q := q) (s := s) (k := k) (t := t) (l := l))=0 := by
  obtain ⟨c,hc,hcover⟩ := exists_countable_graph_cover (s := s) (k := k)
  obtain ⟨d,hd,hcover'⟩ := exists_countable_graph_cover (s := t) (k := l)
  let := hc.toEncodable
  let := hd.toEncodable
  have hn (i : c × d) : μH[finrank ℝ (TupleOperators q s k t l)] (ChartBad i.1.val i.2.val)=0 :=
    chartBad_null i.1.val i.2.val hgap
  apply measure_mono_null (t := ⋃ i : c × d, ChartBad i.1.val i.2.val) ?_ (measure_iUnion_null hn)
  rintro T ⟨P,Q,hPQ⟩
  obtain ⟨F,hFc,hF⟩ := hcover P
  obtain ⟨G,hGd,hG⟩ := hcover' Q
  apply mem_iUnion.mpr
  refine ⟨(⟨F,hFc⟩,⟨G,hGd⟩),slopeCoordinate F P,slopeCoordinate G Q,?_⟩
  have hp : graphPlane F (slopeCoordinate F P).toLinearMap=P.val :=
    congrArg Subtype.val (slopePoint_coordinate F P hF)
  have hq : graphPlane G (slopeCoordinate G Q).toLinearMap=Q.val :=
    congrArg Subtype.val (slopePoint_coordinate G Q hG)
  rw [hp,hq]
  exact hPQ

/-- Existence for the point version, for a fixed forbidden pair of dimensions.
This is a constructed tuple avoiding every actual pair of subspaces. -/
theorem exists_point_incidence_avoiding (hgap : s*k+t*l<q*s*l) :
    ∃ T : TupleOperators q s k t l,
      ∀ (P : Grassmann s k) (Q : Grassmann t l), ¬ ∀ i, ∀ x ∈ P.val, T i x ∈ Q.val := by
  borelize (TupleOperators q s k t l)
  have hn := pointBad_null hgap
  by_contra h
  push Not at h
  have he : PointBad (q := q) (s := s) (k := k) (t := t) (l := l)=univ := Set.eq_univ_of_forall h
  rw [he] at hn
  have hp : 0<μH[finrank ℝ (TupleOperators q s k t l)] (univ : Set (TupleOperators q s k t l)) :=
    isOpen_univ.measure_pos _ Set.univ_nonempty
  exact (ne_of_gt hp) hn

end Kaplansky.Incidence

end

section
open Set Module
namespace Kaplansky.Incidence
open ComplexGrassmann

/-- Extend any subspace to a prescribed intermediate dimension. -/
theorem exists_super_finrank {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (S : Submodule ℂ E) {n : ℕ}
    (hSn : finrank ℂ S≤n) (hn : n≤finrank ℂ E) :
    ∃ U : Submodule ℂ E, S≤U ∧ finrank ℂ U=n := by
  have aux : ∀ j : ℕ, finrank ℂ S+j≤finrank ℂ E →
      ∃ U : Submodule ℂ E, S≤U ∧ finrank ℂ U=finrank ℂ S+j := by
    intro j
    induction j with
    | zero => intro _; exact ⟨S,le_rfl,by omega⟩
    | succ j ih =>
      intro hj
      obtain ⟨U,hSU,hU⟩ := ih (by omega)
      have hu : finrank ℂ U<finrank ℂ E := by omega
      obtain ⟨v,hv⟩ := U.exists_of_finrank_lt hu
      have hv' : v ∉ U := by simpa using hv 1 one_ne_zero
      refine ⟨U ⊔ Submodule.span ℂ {v},hSU.trans le_sup_left,?_⟩
      rw [Submodule.finrank_sup_span_singleton hv',hU]
      omega
  obtain ⟨U,hSU,hU⟩ := aux (n-finrank ℂ S) (by omega)
  exact ⟨U,hSU,by omega⟩

theorem exists_point_expanding_fixed_rank {q s k t l : ℕ} (hgap : s*k+t*l<q*s*l) :
    ∃ T : TupleOperators q s k t l, ∀ S : Submodule ℂ (Components s k),
      finrank ℂ S=s → t<finrank ℂ (⨆ i, S.map (T i).toLinearMap : Submodule ℂ (Components t l)) := by
  obtain ⟨T,hT⟩ := exists_point_incidence_avoiding hgap
  refine ⟨T,fun S hS => ?_⟩
  by_contra h
  have hd : finrank ℂ (⨆ i, S.map (T i).toLinearMap : Submodule ℂ (Components t l))≤t := by omega
  obtain ⟨U,hWU,hU⟩ := exists_super_finrank
    (⨆ i, S.map (T i).toLinearMap : Submodule ℂ (Components t l)) hd (by simp [Components])
  apply hT ⟨S,hS⟩ ⟨U,hU⟩
  intro i x hx
  apply hWU
  apply (le_iSup (fun i => S.map (T i).toLinearMap) i)
  exact Submodule.mem_map.mpr ⟨x,hx,rfl⟩

end Kaplansky.Incidence

end

open scoped MeasureTheory
open Set Module MeasureTheory MeasureTheory.Measure
namespace Kaplansky.Incidence
open ComplexGrassmann

abbrev MatrixTuple (q d r : ℕ) := Fin q → (Fin d → ℂ) →L[ℂ] (Fin r → ℂ)

def RankBad {q d r : ℕ} (s t : ℕ) : Set (MatrixTuple q d r) :=
  {T | ∃ S : Submodule ℂ (Fin d → ℂ), finrank ℂ S=s ∧
    ∃ U : Submodule ℂ (Fin r → ℂ), finrank ℂ U=t ∧ ∀ i, ∀ x ∈ S, T i x ∈ U}

theorem rankBad_null {q d r s t : ℕ} [MeasurableSpace (MatrixTuple q d r)]
    [BorelSpace (MatrixTuple q d r)] (hsd : s≤d) (htr : t≤r)
    (hgap : s*(d-s)+t*(r-t)<q*s*(r-t)) :
    μH[finrank ℝ (MatrixTuple q d r)] (RankBad (q := q) (d := d) (r := r) s t)=0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hsd
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le htr
  have he : RankBad (q := q) (d := s+k) (r := t+l) s t=
      PointBad (q := q) (s := s) (k := k) (t := t) (l := l) := by
    ext T
    constructor
    · rintro ⟨S,hS,U,hU,h⟩
      exact ⟨⟨S,hS⟩,⟨U,hU⟩,h⟩
    · rintro ⟨⟨S,hS⟩,⟨U,hU⟩,h⟩
      exact ⟨S,hS,U,hU,h⟩
  rw [he]
  exact pointBad_null (by simpa using hgap)

theorem exists_point_incidence_tuple {q d r : ℕ} (pairs : Finset (ℕ × ℕ))
    (hpairs : ∀ p ∈ pairs, p.1≤d ∧ p.2≤r ∧
      p.1*(d-p.1)+p.2*(r-p.2)<q*p.1*(r-p.2)) :
    ∃ T : MatrixTuple q d r, ∀ p ∈ pairs, ∀ S : Submodule ℂ (Fin d → ℂ),
      finrank ℂ S=p.1 → p.2<finrank ℂ (⨆ i, S.map (T i).toLinearMap : Submodule ℂ (Fin r → ℂ)) := by
  borelize (MatrixTuple q d r)
  have hn : μH[finrank ℝ (MatrixTuple q d r)] (⋃ p ∈ pairs, RankBad (q := q) (d := d) (r := r) p.1 p.2)=0 :=
    measure_iUnion_null (fun p => measure_iUnion_null (fun hp =>
      rankBad_null (hpairs p hp).1 (hpairs p hp).2.1 (hpairs p hp).2.2))
  have hev : ∃ T : MatrixTuple q d r, T ∉ ⋃ p ∈ pairs, RankBad (q := q) (d := d) (r := r) p.1 p.2 := by
    by_contra h
    push Not at h
    have hu : (⋃ p ∈ pairs, RankBad (q := q) (d := d) (r := r) p.1 p.2)=univ := Set.eq_univ_of_forall h
    rw [hu] at hn
    have hp : 0<μH[finrank ℝ (MatrixTuple q d r)] (univ : Set (MatrixTuple q d r)) :=
      isOpen_univ.measure_pos _ Set.univ_nonempty
    exact (ne_of_gt hp) hn
  obtain ⟨T,hT⟩ := hev
  refine ⟨T,fun p hp S hS => ?_⟩
  by_contra h
  have hd : finrank ℂ (⨆ i, S.map (T i).toLinearMap : Submodule ℂ (Fin r → ℂ))≤p.2 := by omega
  obtain ⟨U,hWU,hU⟩ := exists_super_finrank
    (⨆ i, S.map (T i).toLinearMap : Submodule ℂ (Fin r → ℂ)) hd
      (by simpa using (hpairs p hp).2.1)
  apply hT
  refine Set.mem_iUnion.mpr ⟨p,Set.mem_iUnion.mpr ⟨hp,S,hS,U,hU,?_⟩⟩
  intro i x hx
  apply hWU
  apply (le_iSup (fun i => S.map (T i).toLinearMap) i)
  exact Submodule.mem_map.mpr ⟨x,hx,rfl⟩

theorem point_dimension_inequality_iff {q d r s t : ℕ} (hsd : s≤d) (htr : t≤r) :
    ((q : ℤ)*s-t)*(r-t)-(s : ℤ)*(d-s)>0 ↔
      s*(d-s)+t*(r-t)<q*s*(r-t) := by
  rw [← Int.ofNat_sub hsd,← Int.ofNat_sub htr]
  constructor
  · intro h
    have hh : ((s*(d-s)+t*(r-t) : ℕ) : ℤ)<((q*s*(r-t) : ℕ) : ℤ) := by
      push_cast
      nlinarith
    exact_mod_cast hh
  · intro h
    have hh : ((s*(d-s)+t*(r-t) : ℕ) : ℤ)<((q*s*(r-t) : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at hh
    nlinarith

end Kaplansky.Incidence

end

end OAI
