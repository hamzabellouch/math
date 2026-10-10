import Mathlib
import OAI.GroupTheory.SimpleAmenable.Arithmetic.ConcurrentDenominators
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FlagSites
import OAI.GroupTheory.SimpleAmenable.Arithmetic.QuadraticRectangleCounts
import OAI.GroupTheory.SimpleAmenable.Amenability.BarrierCells

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section BarrierLineGeometry
open Classical Set

noncomputable def barrierLinePoint (a : ℕ) (j : Fin 4) (c : CutRing) (t : ℝ) : ℝ×ℝ :=
  ![(ordinary c,t),(t,ordinary c),(t,ordinary c+Real.goldenRatio^a*t),
    (ordinary c+Real.goldenRatio^a*t,t)] j

noncomputable def barrierLineParameter (j : Fin 4) (p : ℝ×ℝ) : ℝ :=
  ![p.2,p.1,p.1,p.2] j

noncomputable def barrierLineLower (a : ℕ) (j : Fin 4) (c : CutRing) : ℝ :=
  ![0,0,max 0 (-ordinary c/Real.goldenRatio^a),max 0 (-ordinary c/Real.goldenRatio^a)] j

noncomputable def barrierLineUpper (a : ℕ) (j : Fin 4) (c : CutRing) : ℝ :=
  ![1,1,min 1 ((1-ordinary c)/Real.goldenRatio^a),min 1 ((1-ordinary c)/Real.goldenRatio^a)] j

theorem cutForm_barrierLinePoint (a : ℕ) (j : Fin 4) (c : CutRing) (t : ℝ) :
    cutForm a j (barrierLinePoint a j c t)=ordinary c := by
  fin_cases j <;> simp [cutForm,barrierLinePoint]

theorem barrierLineParameter_point (a : ℕ) (j : Fin 4) (c : CutRing) (t : ℝ) :
    barrierLineParameter j (barrierLinePoint a j c t)=t := by
  fin_cases j <;> simp [barrierLineParameter,barrierLinePoint]

theorem barrierLinePoint_parameter {a : ℕ} {j : Fin 4} {c : CutRing} {p : ℝ×ℝ}
    (hp : cutForm a j p=ordinary c) : barrierLinePoint a j c (barrierLineParameter j p)=p := by
  fin_cases j <;> simp [cutForm] at hp <;>
    apply Prod.ext <;> simp [barrierLinePoint,barrierLineParameter] <;> linarith

noncomputable def barrierCandidate (a : ℕ) (j : Fin 4) (N : ℝ) : Set CutRing :=
  {c | |conjugate c|≤4*N ∧ ∃p∈squareInterior,cutForm a j p=ordinary c}

theorem squareInterior_cutForm_bound {a : ℕ} {p : ℝ×ℝ} (hp : p∈squareInterior) (j : Fin 4) :
    |cutForm a j p|≤1+Real.goldenRatio^a := by
  have ht : 0<Real.goldenRatio^a := pow_pos Real.goldenRatio_pos a
  rcases hp with ⟨⟨hx₀,hx₁⟩,⟨hy₀,hy₁⟩⟩
  apply abs_le.mpr
  fin_cases j <;> simp [cutForm] <;> constructor <;> nlinarith

theorem barrierCandidate_finite (a : ℕ) (j : Fin 4) {N : ℝ} (hN : 0<N) :
    (barrierCandidate a j N).Finite := by
  apply (cutRectangle_finite (-(1+Real.goldenRatio^a)) (-4*N)
    (2*(1+Real.goldenRatio^a)) (8*N) (by positivity)).subset
  rintro c ⟨hc,p,hp,hpc⟩
  have hbound := squareInterior_cutForm_bound (a:=a) hp j
  rw [hpc] at hbound
  have ho := abs_le.mp hbound
  have hb := abs_le.mp hc
  exact ⟨⟨ho.1,by linarith [ho.2]⟩,⟨by linarith [hb.1],by linarith [hb.2]⟩⟩

theorem barrierCandidate_coordinate {a : ℕ} {j : Fin 4} {N : ℝ} {c : CutRing}
    (hc : c∈barrierCandidate a j N) (hj : j=0 ∨ j=1) : ordinary c∈Ioo (0:ℝ) 1 := by
  obtain ⟨p,hp,hpc⟩ := hc.2
  rcases hj with rfl | rfl
  · have he : p.1=ordinary c := by simpa [cutForm] using hpc
    exact he ▸ hp.1
  · have he : p.2=ordinary c := by simpa [cutForm] using hpc
    exact he ▸ hp.2

theorem barrierLinePoint_interior_iff {a : ℕ} {j : Fin 4} {N : ℝ} {c : CutRing}
    (hc : c∈barrierCandidate a j N) (t : ℝ) :
    barrierLinePoint a j c t∈squareInterior ↔
      t∈Ioo (barrierLineLower a j c) (barrierLineUpper a j c) := by
  have ht : 0<Real.goldenRatio^a := pow_pos Real.goldenRatio_pos a
  fin_cases j <;> simp [barrierLinePoint,barrierLineLower,barrierLineUpper,
    squareInterior,Set.mem_prod,Set.mem_Ioo]
  · have hz := barrierCandidate_coordinate hc (Or.inl rfl)
    exact fun _ _ => hz
  · have hz := barrierCandidate_coordinate hc (Or.inr rfl)
    exact fun _ _ => hz
  · rw [div_lt_iff₀ ht,lt_div_iff₀ ht]
    constructor <;> intro h <;> constructor <;> constructor <;> linarith [h.1.1,h.1.2,h.2.1,h.2.2]
  · rw [div_lt_iff₀ ht,lt_div_iff₀ ht]
    constructor <;> intro h <;> constructor <;> constructor <;> linarith [h.1.1,h.1.2,h.2.1,h.2.2]

end BarrierLineGeometry

section BarrierFlags
open Classical

noncomputable def barrierTangent (a : ℕ) (j : Fin 4) : ℝ×ℝ :=
  ![(0,1),(1,0),(1,Real.goldenRatio^a),(Real.goldenRatio^a,1)] j

theorem barrierLinePoint_sub (a : ℕ) (j : Fin 4) (c : CutRing) (s t : ℝ) :
    barrierLinePoint a j c s-barrierLinePoint a j c t=(s-t) • barrierTangent a j := by
  fin_cases j <;> apply Prod.ext <;> simp [barrierLinePoint,barrierTangent] <;> ring

theorem barrierTangent_cut (a : ℕ) (j : Fin 4) : cutForm a j (barrierTangent a j)=0 := by
  fin_cases j <;> simp [barrierTangent,cutForm]

theorem positiveDiagonal_transverse {a : ℕ} (ha : 0<a) : TransverseDirection a (1,1) := by
  have ht : 1<Real.goldenRatio^a := one_lt_pow₀ Real.one_lt_goldenRatio (by omega)
  intro j
  fin_cases j <;> simp [cutForm] <;> linarith

theorem exists_barrierFlagDirection {a : ℕ} (ha : 0<a) (j : Fin 4) :
    ∃d : ℝ×ℝ,TransverseDirection a d ∧ 0<d.1 ∧ 0<d.2 ∧ ∀k,
      (cutForm a k d<0 ↔ if cutForm a k (barrierTangent a j)=0 then
        cutForm a k (1,1)<0 else cutForm a k (barrierTangent a j)<0) := by
  obtain ⟨d,hd,he⟩ := flagDirections_sector
    (show FlagDirections a (barrierTangent a j) (1,1) from
      fun k => Or.inr (positiveDiagonal_transverse ha k))
  have ht : 0<Real.goldenRatio^a := pow_pos Real.goldenRatio_pos a
  have hpos₁ : 0<d.1 := by
    have hn : d.1≠0 := by simpa [cutForm] using hd 0
    have hh := he 0
    have hnot : ¬d.1<0 := by
      fin_cases j <;> norm_num [cutForm,barrierTangent,ne_of_gt ht,not_lt_of_gt ht] at hh ⊢ <;> exact hh
    exact lt_of_le_of_ne (le_of_not_gt hnot) hn.symm
  have hpos₂ : 0<d.2 := by
    have hn : d.2≠0 := by simpa [cutForm] using hd 1
    have hh := he 1
    have hnot : ¬d.2<0 := by
      fin_cases j <;> norm_num [cutForm,barrierTangent,ne_of_gt ht,not_lt_of_gt ht] at hh ⊢ <;> exact hh
    exact lt_of_le_of_ne (le_of_not_gt hnot) hn.symm
  exact ⟨d,hd,hpos₁,hpos₂,he⟩

noncomputable def barrierFlagDirection {a : ℕ} (ha : 0<a) (j : Fin 4) : ℝ×ℝ :=
  (exists_barrierFlagDirection ha j).choose

theorem barrierFlagDirection_spec {a : ℕ} (ha : 0<a) (j : Fin 4) :
    TransverseDirection a (barrierFlagDirection ha j) ∧
      0<(barrierFlagDirection ha j).1 ∧ 0<(barrierFlagDirection ha j).2 ∧ ∀k,
      (cutForm a k (barrierFlagDirection ha j)<0 ↔
      if cutForm a k (barrierTangent a j)=0 then cutForm a k (1,1)<0
      else cutForm a k (barrierTangent a j)<0) :=
  (exists_barrierFlagDirection ha j).choose_spec

end BarrierFlags

section BarrierEndpoints
open Classical Set

noncomputable def barrierIncoming (a : ℕ) (j : Fin 4) (c : CutRing) : ℝ×ℝ :=
  barrierLinePoint a j c (barrierLineLower a j c)

theorem barrierLineLower_lt_upper {a : ℕ} {j : Fin 4} {N : ℝ} {c : CutRing}
    (hc : c∈barrierCandidate a j N) : barrierLineLower a j c<barrierLineUpper a j c := by
  obtain ⟨p,hp,hpc⟩ := hc.2
  have hh : barrierLinePoint a j c (barrierLineParameter j p)∈squareInterior := by
    rwa [barrierLinePoint_parameter hpc]
  exact lt_trans ((barrierLinePoint_interior_iff hc _).mp hh).1
    ((barrierLinePoint_interior_iff hc _).mp hh).2

theorem barrierIncoming_bounds {a : ℕ} {j : Fin 4} {N : ℝ} {c : CutRing}
    (hc : c∈barrierCandidate a j N) :
    (barrierIncoming a j c).1∈Ico (0:ℝ) 1 ∧ (barrierIncoming a j c).2∈Ico (0:ℝ) 1 ∧
    ((barrierIncoming a j c).1=0 ∨ (barrierIncoming a j c).2=0) := by
  have ht : 0<Real.goldenRatio^a := pow_pos Real.goldenRatio_pos a
  have hgap := barrierLineLower_lt_upper hc
  fin_cases j
  · have hz := barrierCandidate_coordinate hc (Or.inl rfl)
    simpa [barrierIncoming,barrierLinePoint,barrierLineLower] using
      (show (0≤ordinary c ∧ ordinary c<1) from ⟨le_of_lt hz.1,hz.2⟩)
  · have hz := barrierCandidate_coordinate hc (Or.inr rfl)
    simpa [barrierIncoming,barrierLinePoint,barrierLineLower] using
      (show (0≤ordinary c ∧ ordinary c<1) from ⟨le_of_lt hz.1,hz.2⟩)
  · by_cases h : 0≤ordinary c
    · have hm : max 0 (-ordinary c/Real.goldenRatio^a)=0 :=
        max_eq_left (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h) ht.le)
      simp [barrierLineLower,barrierLineUpper,hm] at hgap
      have hb : ordinary c<1 := by
        have := (div_pos_iff_of_pos_right ht).mp hgap
        linarith
      simp [barrierIncoming,barrierLinePoint,barrierLineLower,hm,h,hb]
    · have hneg : ordinary c<0 := lt_of_not_ge h
      have hm : max 0 (-ordinary c/Real.goldenRatio^a)= -ordinary c/Real.goldenRatio^a :=
        max_eq_right (div_nonneg (neg_nonneg.mpr hneg.le) ht.le)
      simp [barrierLineLower,barrierLineUpper,hm] at hgap
      have he : ordinary c+Real.goldenRatio^a*(-ordinary c/Real.goldenRatio^a)=0 := by
        field_simp; ring
      simp [barrierIncoming,barrierLinePoint,barrierLineLower,he,
        div_nonneg (neg_nonneg.mpr hneg.le) ht.le,hgap.1]
  · by_cases h : 0≤ordinary c
    · have hm : max 0 (-ordinary c/Real.goldenRatio^a)=0 :=
        max_eq_left (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h) ht.le)
      simp [barrierLineLower,barrierLineUpper,hm] at hgap
      have hb : ordinary c<1 := by
        have := (div_pos_iff_of_pos_right ht).mp hgap
        linarith
      simp [barrierIncoming,barrierLinePoint,barrierLineLower,hm,h,hb]
    · have hneg : ordinary c<0 := lt_of_not_ge h
      have hm : max 0 (-ordinary c/Real.goldenRatio^a)= -ordinary c/Real.goldenRatio^a :=
        max_eq_right (div_nonneg (neg_nonneg.mpr hneg.le) ht.le)
      simp [barrierLineLower,barrierLineUpper,hm] at hgap
      have he : ordinary c+Real.goldenRatio^a*(-ordinary c/Real.goldenRatio^a)=0 := by
        field_simp; ring
      simp [barrierIncoming,barrierLinePoint,barrierLineLower,he,
        div_nonneg (neg_nonneg.mpr hneg.le) ht.le,hgap.1]

theorem barrierIncoming_boundary {a : ℕ} (ha : 0<a) {j : Fin 4} {N : ℝ} {c : CutRing}
    (hc : c∈barrierCandidate a j N) :
    SquareBoundary (barrierFlagDirection ha j) (barrierIncoming a j c) := by
  obtain ⟨hx,hy,_⟩ := barrierIncoming_bounds hc
  have hd := barrierFlagDirection_spec ha j
  exact ⟨⟨hx.1,hx.2.le⟩,⟨hy.1,hy.2.le⟩,fun _ => hd.2.1,
    fun h => False.elim ((ne_of_lt hx.2) h),fun _ => hd.2.2.1,
    fun h => False.elim ((ne_of_lt hy.2) h)⟩

theorem barrierIncoming_edge {a : ℕ} {j : Fin 4} {N : ℝ} {c : CutRing}
    (hc : c∈barrierCandidate a j N) : ∃k : Fin 4,k≠j ∧
    cutForm a k (barrierIncoming a j c)=ordinary (0:CutRing) := by
  obtain ⟨hx,hy,hzero⟩ := barrierIncoming_bounds hc
  have hj := cutForm_barrierLinePoint a j c (barrierLineLower a j c)
  change cutForm a j (barrierIncoming a j c)=ordinary c at hj
  by_cases hj₀ : j=0
  · subst j
    refine ⟨1,by decide,?_⟩
    have hcpos := (barrierCandidate_coordinate hc (Or.inl rfl)).1
    have hxne : (barrierIncoming a 0 c).1≠0 := by
      simp [cutForm] at hj
      rw [hj]; exact ne_of_gt hcpos
    simpa [cutForm] using hzero.resolve_left hxne
  · rcases hzero with hzero | hzero
    · exact ⟨0,Ne.symm hj₀,by simpa [cutForm] using hzero⟩
    · refine ⟨1,?_,by simpa [cutForm] using hzero⟩
      intro he
      subst j
      have hcpos := (barrierCandidate_coordinate hc (Or.inr rfl)).1
      simp [cutForm] at hj
      linarith

theorem barrierIncoming_lattice {a : ℕ} (ha : 0<a) {j : Fin 4} {N : ℝ} {c : CutRing}
    (hc : c∈barrierCandidate a j N) :
    InFlagLattice (commonVertexDenominator a) (barrierIncoming a j c) := by
  obtain ⟨k,hkj,hk⟩ := barrierIncoming_edge hc
  obtain ⟨u,v,hu,hv⟩ := all_intersections_common_denominator ha j k hkj.symm c 0
    (barrierIncoming a j c) (cutForm_barrierLinePoint a j c _) hk
  refine ⟨(u,v),Prod.ext ?_ ?_⟩ <;> simp only [scaledOrdinary]
  · rw [hu,mul_div_cancel_left₀ _ (by exact_mod_cast Nat.ne_of_gt (commonVertexDenominator_pos ha))]
  · rw [hv,mul_div_cancel_left₀ _ (by exact_mod_cast Nat.ne_of_gt (commonVertexDenominator_pos ha))]

noncomputable def barrierIncomingSite {a m : ℕ} (ha : 0<a) (i : Fin m)
    {j : Fin 4} {N : ℝ} {c : CutRing} (hc : c∈barrierCandidate a j N) :
    FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) :=
  ⟨(i,⟨barrierIncoming a j c,(barrierFlagDirection_spec ha j).1,barrierIncoming_boundary ha hc⟩),
    barrierIncoming_lattice ha hc⟩

end BarrierEndpoints

end SimpleAmenable
end
end

end OAI
