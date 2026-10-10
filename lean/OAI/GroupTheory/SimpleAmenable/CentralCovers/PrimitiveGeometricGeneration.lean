import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.TrackTranslationChart
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.Supported

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PrimitiveGeometricGeneration

theorem cutForm_sub (a : ℕ) (j : Fin 4) (p q : ℝ × ℝ) :
    cutForm a j (p-q) = cutForm a j p - cutForm a j q := by
  fin_cases j <;> simp [cutForm] <;> ring

private theorem fract_small_lift {r x : ℝ} (hr : 0 < r ∧ r < 1/2)
    (hx : -r < x ∧ x < r) : ∃ k : Fin 2, Int.fract x = x + k.val := by
  by_cases hx0 : 0 ≤ x
  · refine ⟨0,?_⟩
    simp only [Fin.val_zero,Nat.cast_zero,add_zero]
    exact Int.fract_eq_self.mpr ⟨hx0,by linarith⟩
  · refine ⟨1,?_⟩
    have hf : ⌊x⌋ = (-1 : ℤ) := Int.floor_eq_iff.mpr (by constructor <;> norm_num <;> linarith)
    simp [Int.fract,hf]

private theorem fract_small_lift_unique {r x : ℝ} (hr : 0 < r ∧ r < 1/2)
    (hx : -r < x ∧ x < r) (k : Fin 2)
    (hk : -r ≤ Int.fract x - k.val ∧ Int.fract x - k.val < r) :
    Int.fract x - k.val = x := by
  obtain ⟨j,hj⟩ := fract_small_lift hr hx
  fin_cases j <;> fin_cases k <;>
    simp only [Nat.cast_zero,Nat.cast_one,add_zero,sub_zero] at hj hk ⊢ <;>
    linarith

theorem mem_circularBoxPiece {a : ℕ} (r : CutRing) (k : Fin 2 × Fin 2)
    (p : GenericSquare a) : p ∈ (circularBoxPiece a r k).val ↔
    (-ordinary r ≤ p.val.1-k.1.val ∧ p.val.1-k.1.val < ordinary r) ∧
    (-ordinary r ≤ p.val.2-k.2.val ∧ p.val.2-k.2.val < ordinary r) := by
  simp only [circularBoxPiece,Set.mem_inter_iff,Set.mem_compl_iff,halfPlane,
    Set.mem_ofPred_eq,not_lt,cutForm,Matrix.cons_val_zero,Matrix.cons_val_one,
    map_add,map_neg,map_natCast]
  constructor <;> rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩ <;> constructor <;> constructor <;> linarith

theorem mem_clippedSlope_lift {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (p : GenericSquare a) (t : ℝ × ℝ)
    (ht : (-ordinary r < t.1 ∧ t.1 < ordinary r) ∧
      (-ordinary r < t.2 ∧ t.2 < ordinary r))
    (hp : p.val = (Int.fract t.1,Int.fract t.2)) :
    p ∈ (clippedSlopePrimitive a r j).val ↔ 0 ≤ cutForm a j t := by
  classical
  have hform (k : Fin 2 × Fin 2)
      (hk : (p.val.1-k.1.val,p.val.2-k.2.val) = t) :
      cutForm a j p.val - ordinary (integralCutForm a j (k.1.val,k.2.val)) =
        cutForm a j t := by
    rw [← cutForm_ordinary,← cutForm_sub]
    simpa only [map_natCast,Prod.sub_def] using congrArg (cutForm a j) hk
  constructor
  · intro h
    obtain ⟨k,hk,hside⟩ := Set.mem_iUnion.mp h
    have hb := (mem_circularBoxPiece r k p).mp hk
    have he : (p.val.1-k.1.val,p.val.2-k.2.val) = t := by
      apply Prod.ext
      · simpa only [hp] using fract_small_lift_unique hr ht.1 k.1 (by simpa only [hp] using hb.1)
      · simpa only [hp] using fract_small_lift_unique hr ht.2 k.2 (by simpa only [hp] using hb.2)
    have hs : ordinary (integralCutForm a j (k.1.val,k.2.val)) ≤ cutForm a j p.val := not_lt.mp hside
    linarith [hform k he]
  · intro h
    obtain ⟨kx,hx⟩ := fract_small_lift hr ht.1
    obtain ⟨ky,hy⟩ := fract_small_lift hr ht.2
    let k : Fin 2 × Fin 2 := (kx,ky)
    have he : (p.val.1-k.1.val,p.val.2-k.2.val) = t := by
      simp [hp,k,hx,hy]
    apply Set.mem_iUnion.mpr
    refine ⟨k,(mem_circularBoxPiece r k p).mpr ?_,?_⟩
    · have h1 : p.val.1-k.1.val = t.1 := congrArg Prod.fst he
      have h2 : p.val.2-k.2.val = t.2 := congrArg Prod.snd he
      constructor <;> constructor <;> linarith [ht.1.1,ht.1.2,ht.2.1,ht.2.2]
    · change ¬cutForm a j p.val < ordinary (integralCutForm a j (k.1.val,k.2.val))
      linarith [hform k he]

theorem translated_clippedSlope_local {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (u : CutRing × CutRing)
    (p : GenericSquare a)
    (hp : (-ordinary r < p.val.1-ordinary u.1 ∧ p.val.1-ordinary u.1 < ordinary r) ∧
      (-ordinary r < p.val.2-ordinary u.2 ∧ p.val.2-ordinary u.2 < ordinary r)) :
    translate a (-u) p ∈ (clippedSlopePrimitive a r j).val ↔
      ordinary (integralCutForm a j u) ≤ cutForm a j p.val := by
  rw [mem_clippedSlope_lift r j hr (translate a (-u) p)
    (p.val - (ordinary u.1,ordinary u.2)) hp (by simp [sub_eq_add_neg])]
  rw [cutForm_sub,cutForm_ordinary]
  exact sub_nonneg

private theorem exists_cut_parameter (f : ℝ → ℝ × ℝ) (hf : Continuous f)
    (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : CutRing, dist (f (ordinary u)) (f x) < ε := by
  exact ordinary_denseRange.exists_mem_open (hf.isOpen_preimage _ Metric.isOpen_ball)
    ⟨x,by simpa using hε⟩

theorem slope_line_anchor (a : ℕ) (j : Fin 4) (hj : j = 2 ∨ j = 3)
    (z : CutRing) (p : ℝ × ℝ) (hp : cutForm a j p = ordinary z)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : CutRing × CutRing, integralCutForm a j u = z ∧
      dist (ordinary u.1,ordinary u.2) p < ε := by
  rcases hj with rfl | rfl
  · let f : ℝ → ℝ × ℝ := fun x => (x,ordinary z + Real.goldenRatio^a*x)
    have hf : Continuous f := continuous_id.prodMk (continuous_const.add (continuous_const.mul continuous_id))
    obtain ⟨u,hu⟩ := exists_cut_parameter f hf p.1 hε
    have he : f p.1 = p := by
      apply Prod.ext
      · rfl
      · change ordinary z + Real.goldenRatio^a*p.1 = p.2
        simp [cutForm] at hp
        linarith
    refine ⟨(u,z+cutTau^a*u),?_,?_⟩
    · simp [integralCutForm]
    · simpa only [f,map_add,map_mul,map_pow,ordinary_cutTau,he] using hu
  · let f : ℝ → ℝ × ℝ := fun y => (ordinary z + Real.goldenRatio^a*y,y)
    have hf : Continuous f := (continuous_const.add (continuous_const.mul continuous_id)).prodMk continuous_id
    obtain ⟨u,hu⟩ := exists_cut_parameter f hf p.2 hε
    have he : f p.2 = p := by
      apply Prod.ext
      · change ordinary z + Real.goldenRatio^a*p.2 = p.1
        simp [cutForm] at hp
        linarith
      · rfl
    refine ⟨(z+cutTau^a*u,u),?_,?_⟩
    · simp [integralCutForm]
    · simpa only [f,map_add,map_mul,map_pow,ordinary_cutTau,he] using hu

noncomputable def ordinaryBox (l h : CutRing × CutRing) : Set (ℝ × ℝ) :=
  Set.Ioo (ordinary l.1) (ordinary h.1) ×ˢ Set.Ioo (ordinary l.2) (ordinary h.2)

noncomputable def genericBox (a : ℕ) (l h : CutRing × CutRing) : Set (GenericSquare a) :=
  Subtype.val ⁻¹' ordinaryBox l h

theorem genericBox_eq {a : ℕ} (l h : CutRing × CutRing) : genericBox a l h =
    ((halfPlane a 0 l.1)ᶜ ∩ halfPlane a 0 h.1) ∩
      ((halfPlane a 1 l.2)ᶜ ∩ halfPlane a 1 h.2) := by
  ext p
  have hx : p.val.1 ≠ ordinary l.1 := p.property.2.2 0 l.1
  have hy : p.val.2 ≠ ordinary l.2 := p.property.2.2 1 l.2
  simp only [genericBox,ordinaryBox,
    Set.mem_inter_iff,Set.mem_compl_iff,halfPlane,Set.mem_ofPred_eq,cutForm,
    Matrix.cons_val_zero,Matrix.cons_val_one,not_lt]
  exact and_congr (and_congr (lt_iff_le_and_ne.trans (and_iff_left hx.symm)) Iff.rfl)
    (and_congr (lt_iff_le_and_ne.trans (and_iff_left hy.symm)) Iff.rfl)

theorem genericBox_mem {a : ℕ} (B : BooleanSubalgebra (Set (GenericSquare a)))
    (hcoord : ∀ (j : Fin 2) z, halfPlane a (Fin.castLE (by omega) j) z ∈ B)
    (l h : CutRing × CutRing) : genericBox a l h ∈ B := by
  rw [genericBox_eq]
  exact BooleanSubalgebra.inf_mem
    (BooleanSubalgebra.inf_mem (BooleanSubalgebra.compl_mem (hcoord 0 l.1)) (hcoord 0 h.1))
    (BooleanSubalgebra.inf_mem (BooleanSubalgebra.compl_mem (hcoord 1 l.2)) (hcoord 1 h.2))

theorem exists_box_in_open {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (p : ℝ × ℝ) (hp : p ∈ U) :
    ∃ l h : CutRing × CutRing, p ∈ ordinaryBox l h ∧ ordinaryBox l h ⊆ U := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU p hp
  obtain ⟨l₁,hl₁,hlp⟩ := exists_cut_between (show p.1-ε < p.1 by linarith)
  obtain ⟨l₂,hl₂,hlq⟩ := exists_cut_between (show p.2-ε < p.2 by linarith)
  obtain ⟨h₁,hph,hh₁⟩ := exists_cut_between (show p.1 < p.1+ε by linarith)
  obtain ⟨h₂,hqh,hh₂⟩ := exists_cut_between (show p.2 < p.2+ε by linarith)
  refine ⟨(l₁,l₂),(h₁,h₂),⟨⟨hlp,hph⟩,⟨hlq,hqh⟩⟩,?_⟩
  rintro q ⟨⟨hqx,hqx'⟩,⟨hqy,hqy'⟩⟩
  apply hball
  change max (dist q.1 p.1) (dist q.2 p.2) < ε
  rw [max_lt_iff,Real.dist_eq,Real.dist_eq,abs_lt,abs_lt]
  constructor <;> constructor <;> linarith

theorem halfPlane_locally_generated {a : ℕ} (r : CutRing)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (B : BooleanSubalgebra (Set (GenericSquare a)))
    (htrans : ∀ u U, U ∈ B → translate a u ⁻¹' U ∈ B)
    (j : Fin 4) (hj : j = 2 ∨ j = 3)
    (hprimitive : (clippedSlopePrimitive a r j).val ∈ B)
    (z : CutRing) (p : ℝ × ℝ) :
    ∃ l h : CutRing × CutRing, ∃ D : Set (GenericSquare a),
      p ∈ ordinaryBox l h ∧ D ∈ B ∧
      ∀ q : GenericSquare a, q.val ∈ ordinaryBox l h →
        (q ∈ halfPlane a j z ↔ q ∈ D) := by
  rcases lt_trichotomy (cutForm a j p) (ordinary z) with hp | hp | hp
  · obtain ⟨l,h,hl,hsub⟩ := exists_box_in_open
      (isOpen_lt (cutForm_continuous a j) continuous_const) p hp
    refine ⟨l,h,Set.univ,hl,BooleanSubalgebra.top_mem,?_⟩
    intro q hq
    exact iff_true_intro (hsub hq)
  · obtain ⟨u,hu,hup⟩ := slope_line_anchor a j hj z p hp hr.1
    have hpU : p ∈ {q : ℝ × ℝ |
        (-ordinary r < q.1-ordinary u.1 ∧ q.1-ordinary u.1 < ordinary r) ∧
        (-ordinary r < q.2-ordinary u.2 ∧ q.2-ordinary u.2 < ordinary r)} := by
      change max (dist (ordinary u.1) p.1) (dist (ordinary u.2) p.2) < ordinary r at hup
      rw [max_lt_iff,Real.dist_eq,Real.dist_eq,abs_lt,abs_lt] at hup
      exact ⟨⟨by linarith [hup.1.2],by linarith [hup.1.1]⟩,
        ⟨by linarith [hup.2.2],by linarith [hup.2.1]⟩⟩
    have hU : IsOpen {q : ℝ × ℝ |
        (-ordinary r < q.1-ordinary u.1 ∧ q.1-ordinary u.1 < ordinary r) ∧
        (-ordinary r < q.2-ordinary u.2 ∧ q.2-ordinary u.2 < ordinary r)} :=
      ((isOpen_lt continuous_const (continuous_fst.sub continuous_const)).inter
        (isOpen_lt (continuous_fst.sub continuous_const) continuous_const)).inter
      ((isOpen_lt continuous_const (continuous_snd.sub continuous_const)).inter
        (isOpen_lt (continuous_snd.sub continuous_const) continuous_const))
    obtain ⟨l,h,hl,hsub⟩ := exists_box_in_open hU p hpU
    refine ⟨l,h,(translate a (-u) ⁻¹' (clippedSlopePrimitive a r j).val)ᶜ,hl,
      BooleanSubalgebra.compl_mem (htrans _ _ hprimitive),?_⟩
    intro q hq
    change cutForm a j q.val < ordinary z ↔ ¬translate a (-u) q ∈ (clippedSlopePrimitive a r j).val
    rw [translated_clippedSlope_local r j hr u q (hsub hq),hu,not_le]
  · obtain ⟨l,h,hl,hsub⟩ := exists_box_in_open
      (isOpen_lt continuous_const (cutForm_continuous a j)) p hp
    refine ⟨l,h,∅,hl,BooleanSubalgebra.bot_mem,?_⟩
    intro q hq
    change cutForm a j q.val < ordinary z ↔ False
    exact iff_false_intro (not_lt.mpr (le_of_lt (hsub hq)))

theorem slope_cuts_generated {a : ℕ} (r : CutRing)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (B : BooleanSubalgebra (Set (GenericSquare a)))
    (htrans : ∀ u U, U ∈ B → translate a u ⁻¹' U ∈ B)
    (hcoord : ∀ (j : Fin 2) z, halfPlane a (Fin.castLE (by omega) j) z ∈ B)
    (j : Fin 4) (hj : j = 2 ∨ j = 3)
    (hprimitive : (clippedSlopePrimitive a r j).val ∈ B) (z : CutRing) :
    halfPlane a j z ∈ B := by
  classical
  choose l h D hp hD he using halfPlane_locally_generated r hr B htrans j hj hprimitive z
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun p => ordinaryBox (l p) (h p))
    (fun _ => isOpen_Ioo.prod isOpen_Ioo) (by intro p _; exact Set.mem_iUnion.mpr ⟨p,hp p⟩)
  have heq : halfPlane a j z = ⋃ p ∈ s, genericBox a (l p) (h p) ∩ D p := by
    ext q
    constructor
    · intro hq
      have hqK : q.val ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
        ⟨⟨q.property.1.1,q.property.1.2.le⟩,⟨q.property.2.1.1,q.property.2.1.2.le⟩⟩
      obtain ⟨p,hps,hqp⟩ := Set.mem_iUnion₂.mp (hs hqK)
      exact Set.mem_iUnion₂.mpr ⟨p,hps,hqp,(he p q hqp).mp hq⟩
    · intro hq
      obtain ⟨p,_,hqp,hqD⟩ := Set.mem_iUnion₂.mp hq
      exact (he p q hqp).mpr hqD
  rw [heq]
  exact BooleanSubalgebra.biSup_mem s.finite_toSet (fun p _ =>
    BooleanSubalgebra.inf_mem (genericBox_mem B hcoord _ _) (hD p))

end PrimitiveGeometricGeneration

end SimpleAmenable
end
end

end OAI
