import Mathlib
import OAI.GroupTheory.SimpleAmenable.Arithmetic.ConcurrentDenominators
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PlaneCornerInjectivity

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PlaneCornerKernel
open Classical

noncomputable def planePairValue {a : ℕ} (f : PlaneStep a) (z v : ℝ × ℝ) : ℤ :=
  planeGerm f z v+planeGerm f z (-v)

noncomputable def planeCornerValue {a : ℕ} (f : PlaneStep a) (z v : ℝ × ℝ) : ℤ :=
  planePairValue f z v-planePairValue f z (-1,1)

@[simp] theorem planeCornerValue_zero {a : ℕ} (z v : ℝ × ℝ) :
    planeCornerValue (0 : PlaneStep a) z v=0 := by simp [planeCornerValue,planePairValue]

@[simp] theorem planeCornerValue_add {a : ℕ} (f g : PlaneStep a) (z v : ℝ × ℝ) :
    planeCornerValue (f+g) z v=planeCornerValue f z v+planeCornerValue g z v := by
  simp only [planeCornerValue,planePairValue,planeGerm_add]; ring

@[simp] theorem planeCornerValue_smul {a : ℕ} (c : ℤ) (f : PlaneStep a) (z v : ℝ × ℝ) :
    planeCornerValue (c • f) z v=c • planeCornerValue f z v := by
  simp only [planeCornerValue,planePairValue,planeGerm_smul,smul_add,smul_sub]

def planeSupportClosure {a : ℕ} (f : PlaneStep a) : Set (ℝ × ℝ) :=
  closure {z | ∃ p : GenericPlane a, p.val=z ∧ f.val p≠0}

theorem planeSupportClosure_compact {a : ℕ} (f : PlaneStep a) :
    IsCompact (planeSupportClosure f) := by
  obtain ⟨R,hR⟩ := PlaneStep.compactSupport f
  have hcompact : IsCompact (Set.Icc (-R) R ×ˢ Set.Icc (-R) R) :=
    isCompact_Icc.prod isCompact_Icc
  apply hcompact.of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_Icc.prod isClosed_Icc)
  rintro _ ⟨p,rfl,hp⟩
  have h : |p.val.1|≤R ∧ |p.val.2|≤R := by
    constructor
    · by_contra! hh
      exact hp (hR p (Or.inl hh))
    · by_contra! hh
      exact hp (hR p (Or.inr hh))
  exact ⟨abs_le.mp h.1,abs_le.mp h.2⟩

theorem planeSupportClosure_nonempty {a : ℕ} {f : PlaneStep a} (hf : f≠0) :
    (planeSupportClosure f).Nonempty := by
  have hh : ∃ p : GenericPlane a, f.val p≠0 := by
    by_contra! h
    apply hf
    apply Subtype.ext
    funext p
    exact h p
  obtain ⟨p,hp⟩ := hh
  exact ⟨p.val,subset_closure ⟨p,rfl,hp⟩⟩

theorem planeGerm_zero_at_minimum {a : ℕ} (f : PlaneStep a) {z v : ℝ × ℝ}
    (hmin : ∀ p : GenericPlane a, f.val p≠0 → planeHeight z≤planeHeight p.val)
    (hv : TransverseDirection a v) (hdesc : planeHeight v<0) :
    planeGerm f z v=0 := by
  obtain ⟨N,hN,hz,hf⟩ := planeGerm_spec f z v hv
  obtain ⟨p,hp,hpv,hdown⟩ := planeSector_generic_descending hv hdesc hN hz
  by_contra hh
  have hp' : f.val p≠0 := by rwa [hf p hp hpv]
  exact (not_lt_of_ge (hmin p hp')) hdown

theorem planeGerm_zero_at_minimum_le {a : ℕ} (f : PlaneStep a) {z v : ℝ × ℝ}
    (hmin : ∀ p : GenericPlane a, f.val p≠0 → planeHeight z≤planeHeight p.val)
    (hv : TransverseDirection a v) (hdesc : planeHeight v≤0) :
    planeGerm f z v=0 := by
  obtain ⟨w,hw,hdown,hvw⟩ := transverse_negative_perturbation hv hdesc
  exact (planeGerm_congr_direction f z hv hw hvw).trans
    (planeGerm_zero_at_minimum f hmin hw hdown)

theorem planeCornerValue_injective_zero {a : ℕ} (f : PlaneStep a)
    (hc : ∀ z v, TransverseDirection a v → planeCornerValue f z v=0) : f=0 := by
  by_contra hf
  obtain ⟨z,hz,hmin⟩ := (planeSupportClosure_compact f).exists_isMinOn
    (planeSupportClosure_nonempty hf) planeHeight_continuous.continuousOn
  have hminimum : ∀ p : GenericPlane a, f.val p≠0 → planeHeight z≤planeHeight p.val := by
    intro p hp
    exact hmin (subset_closure ⟨p,rfl,hp⟩)
  have hbase : planePairValue f z (-1,1)=0 := by
    unfold planePairValue
    rw [planeGerm_zero_at_minimum_le f hminimum (plane_antidiagonal_transverse a)
      (by norm_num [planeHeight])]
    rw [planeGerm_zero_at_minimum_le f hminimum (plane_antidiagonal_transverse a).neg
      (by norm_num [planeHeight])]
    simp
  have hzero : ∀ v, TransverseDirection a v → planeGerm f z v=0 := by
    intro v hv
    have he := hc z v hv
    unfold planeCornerValue at he
    rw [hbase,sub_zero] at he
    change planeGerm f z v+planeGerm f z (-v)=0 at he
    by_cases hh : planeHeight v≤0
    · exact planeGerm_zero_at_minimum_le f hminimum hv hh
    · have hn : planeHeight (-v)≤0 := by
        change -v.1+-v.2≤0
        change ¬v.1+v.2≤0 at hh
        linarith
      rw [planeGerm_zero_at_minimum_le f hminimum hv.neg hn,add_zero] at he
      exact he
  obtain ⟨N,hN,hzN,hfN⟩ := planeGerm_zero_neighborhood f z hzero
  obtain ⟨_,hpN,p,rfl,hp⟩ := mem_closure_iff.mp hz N hN hzN
  exact hp (hfN p hpN)

end PlaneCornerKernel

section PlaneCornerSupport
open Classical

theorem planeGerm_congr_incident {a : ℕ} (f : PlaneStep a) {S : Finset PlaneCut}
    (hS : ∀ p q, (∀ l∈S, planeSign l p=planeSign l q) → f.val p=f.val q)
    (z : ℝ × ℝ) {v w : ℝ × ℝ} (hv : TransverseDirection a v)
    (hw : TransverseDirection a w)
    (he : ∀ l∈S, cutForm a l.1 z=ordinary l.2 →
      (cutForm a l.1 v<0 ↔ cutForm a l.1 w<0)) :
    planeGerm f z v=planeGerm f z w := by
  obtain ⟨p,hp,hpv⟩ := planeSector_generic hv (arrangementNeighborhood_open a S z)
    (self_mem_arrangementNeighborhood a S z)
  obtain ⟨q,hq,hqv⟩ := planeSector_generic hw (arrangementNeighborhood_open a S z)
    (self_mem_arrangementNeighborhood a S z)
  rw [← planeGerm_evaluate f hS hv hp hpv,← planeGerm_evaluate f hS hw hq hqv]
  apply hS
  intro l hl
  rw [planeSign_neighborhood hp hpv hl,planeSign_neighborhood hq hqv hl]
  apply decide_eq_decide.mpr
  split_ifs with hh
  · exact he l hl hh
  · rfl

theorem planeCornerValue_zero_of_one_direction {a : ℕ} (f : PlaneStep a)
    {S : Finset PlaneCut}
    (hS : ∀ p q, (∀ l∈S, planeSign l p=planeSign l q) → f.val p=f.val q)
    (z : ℝ × ℝ) (j : Fin 4)
    (hj : ∀ l∈S, cutForm a l.1 z=ordinary l.2 → l.1=j)
    {v : ℝ × ℝ} (hv : TransverseDirection a v) : planeCornerValue f z v=0 := by
  let w : ℝ × ℝ := (-1,1)
  have hw : TransverseDirection a w := plane_antidiagonal_transverse a
  have hcompare : ∀ {x y : ℝ × ℝ}, TransverseDirection a x → TransverseDirection a y →
      (cutForm a j x<0 ↔ cutForm a j y<0) → planeGerm f z x=planeGerm f z y := by
    intro x y hx hy he
    apply planeGerm_congr_incident f hS z hx hy
    intro l hl hz
    simpa only [hj l hl hz] using he
  by_cases he : (cutForm a j v<0 ↔ cutForm a j w<0)
  · have he' : (cutForm a j (-v)<0 ↔ cutForm a j (-w)<0) := by
      simp only [cutForm_neg,neg_lt_zero]
      constructor
      · intro h
        by_contra! hh
        have hw' := hw j
        have hh' : cutForm a j w<0 := lt_of_le_of_ne hh hw'
        have := he.mpr hh'; linarith
      · intro h
        by_contra! hh
        have hv' := hv j
        have hh' : cutForm a j v<0 := lt_of_le_of_ne hh hv'
        have := he.mp hh'; linarith
    have h₁ := hcompare hv hw he
    have h₂ := hcompare hv.neg hw.neg he'
    unfold planeCornerValue planePairValue
    change planeGerm f z v+planeGerm f z (-v)-(planeGerm f z w+planeGerm f z (-w))=0
    rw [h₁,h₂,sub_self]
  · have he₁ : (cutForm a j v<0 ↔ cutForm a j (-w)<0) := by
      rw [cutForm_neg,neg_lt_zero]
      have hv' := hv j
      have hw' := hw j
      constructor <;> intro hh
      · by_contra! ht
        have hwlt : cutForm a j w<0 := lt_of_le_of_ne ht hw'
        exact he (iff_of_true hh hwlt)
      · by_contra! ht
        have hvlt : 0<cutForm a j v := lt_of_le_of_ne ht hv'.symm
        exact he (iff_of_false (not_lt_of_gt hvlt) (not_lt_of_gt hh))
    have he₂ : (cutForm a j (-v)<0 ↔ cutForm a j w<0) := by
      rw [cutForm_neg,neg_lt_zero]
      have hv' := hv j
      have hw' := hw j
      constructor <;> intro hh
      · by_contra! ht
        have hwlt : 0<cutForm a j w := lt_of_le_of_ne ht hw'.symm
        exact he (iff_of_false (not_lt_of_gt hh) (not_lt_of_gt hwlt))
      · by_contra! ht
        have hvlt : cutForm a j v<0 := lt_of_le_of_ne ht hv'
        exact he (iff_of_true hvlt hh)
    have h₁ := hcompare hv hw.neg he₁
    have h₂ := hcompare hv.neg hw he₂
    unfold planeCornerValue planePairValue
    change planeGerm f z v+planeGerm f z (-v)-(planeGerm f z w+planeGerm f z (-w))=0
    rw [h₁,h₂]
    ring

theorem plane_line_intersection_unique {a : ℕ} (ha : 0<a) {i j : Fin 4} (hij : i≠j)
    {p q : ℝ × ℝ} (hi : cutForm a i p=cutForm a i q)
    (hj : cutForm a j p=cutForm a j q) : p=q := by
  have hd : ordinary (lineDet a i j)≠0 := fun hh =>
    lineDet_ne_zero ha i j hij (ordinary_injective (by simpa using hh))
  rw [cutForm_normal,cutForm_normal] at hi hj
  have h₁ : ordinary (lineDet a i j)*(p.1-q.1)=0 := by
    simp only [lineDet,map_sub,map_mul]
    linear_combination ordinary (lineNormal a j).2*hi-ordinary (lineNormal a i).2*hj
  have h₂ : ordinary (lineDet a i j)*(p.2-q.2)=0 := by
    simp only [lineDet,map_sub,map_mul]
    linear_combination ordinary (lineNormal a i).1*hj-ordinary (lineNormal a j).1*hi
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp h₁).resolve_left hd))
    (sub_eq_zero.mp ((mul_eq_zero.mp h₂).resolve_left hd))

noncomputable def planeLineIntersection (a : ℕ) (l k : PlaneCut) : ℝ × ℝ :=
  if h : ∃ z, cutForm a l.1 z=ordinary l.2 ∧ cutForm a k.1 z=ordinary k.2 then
    Classical.choose h else 0

theorem planeLineIntersection_eq {a : ℕ} (ha : 0<a) {l k : PlaneCut}
    (hdir : l.1≠k.1) {z : ℝ × ℝ}
    (hl : cutForm a l.1 z=ordinary l.2) (hk : cutForm a k.1 z=ordinary k.2) :
    planeLineIntersection a l k=z := by
  have he : ∃ z, cutForm a l.1 z=ordinary l.2 ∧ cutForm a k.1 z=ordinary k.2 := ⟨z,hl,hk⟩
  rw [planeLineIntersection,dite_eq_left he]
  have hh := Classical.choose_spec he
  exact plane_line_intersection_unique ha hdir (hh.1.trans hl.symm) (hh.2.trans hk.symm)

noncomputable def planeArrangementVertices (a : ℕ) (S : Finset PlaneCut) : Finset (ℝ × ℝ) :=
  (S.product S).image (fun lk => planeLineIntersection a lk.1 lk.2)

theorem planeCornerValue_exists_incident {a : ℕ} (f : PlaneStep a) {S : Finset PlaneCut}
    (hS : ∀ p q, (∀ l∈S, planeSign l p=planeSign l q) → f.val p=f.val q)
    {z v : ℝ × ℝ} (hv : TransverseDirection a v) (hc : planeCornerValue f z v≠0) :
    ∃ l∈S, ∃ k∈S, l.1≠k.1 ∧ cutForm a l.1 z=ordinary l.2 ∧
      cutForm a k.1 z=ordinary k.2 := by
  by_contra! h
  by_cases hinc : ∃ l∈S, cutForm a l.1 z=ordinary l.2
  · obtain ⟨l,hl,hzl⟩ := hinc
    apply hc
    apply planeCornerValue_zero_of_one_direction f hS z l.1 _ hv
    intro k hk hzk
    by_contra hdir
    exact (h k hk l hl hdir hzk) hzl
  · apply hc
    apply planeCornerValue_zero_of_one_direction f hS z 0 _ hv
    intro l hl hzl
    exact (hinc ⟨l,hl,hzl⟩).elim

theorem planeCornerValue_mem_vertices {a : ℕ} (ha : 0<a) (f : PlaneStep a)
    {S : Finset PlaneCut}
    (hS : ∀ p q, (∀ l∈S, planeSign l p=planeSign l q) → f.val p=f.val q)
    {z v : ℝ × ℝ} (hv : TransverseDirection a v) (hc : planeCornerValue f z v≠0) :
    z∈planeArrangementVertices a S := by
  obtain ⟨l,hl,k,hk,hdir,hzl,hzk⟩ := planeCornerValue_exists_incident f hS hv hc
  exact Finset.mem_image.mpr ⟨(l,k),Finset.mem_product.mpr ⟨hl,hk⟩,
    planeLineIntersection_eq ha hdir hzl hzk⟩

end PlaneCornerSupport

end SimpleAmenable
end
end

end OAI
