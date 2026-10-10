import OAI.Analysis.DiamondDistortion.UpperFunction

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace RecursiveModel

section
variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal)
lemma fullUpper_neg (h : ℕ) (v : Full p h) :
    fullUpper p hp h (-v)=((fullUpper p hp h v).2,(fullUpper p hp h v).1) := by
  induction h with
  | zero => simp only [fullUpper_zero_height,lp.coeFn_neg,Pi.neg_apply,neg_neg]
  | succ h ih =>
    have hP : fullPChildren p hp h (-v)=fullQChildren p hp h v := by
      ext i; rw [fullPChildren_apply,fullQChildren_apply,child_neg,ih]
    have hQ : fullQChildren p hp h (-v)=fullPChildren p hp h v := by
      ext i; rw [fullQChildren_apply,fullPChildren_apply,child_neg,ih]
    rw [fullUpper_succ,fullUpper_succ,hP,hQ]
    change join (-v (.inl ())) _ _=(_,_)
    ext <;> dsimp only [join,Prod.fst,Prod.snd]
    · rw [max_comm]; congr 1; ring
    · rw [max_comm]; congr 1; ring

lemma fullUpper_add (h : ℕ) (v w : Full p h) :
    (fullUpper p hp h (v+w)).1 ≤ (fullUpper p hp h v).1+(fullUpper p hp h w).1 ∧
    (fullUpper p hp h (v+w)).2 ≤ (fullUpper p hp h v).2+(fullUpper p hp h w).2 := by
  induction h with
  | zero =>
    change max (v ()+w ()) 0 ≤ max (v ()) 0+max (w ()) 0 ∧
      max (-(v ()+w ())) 0 ≤ max (-v ()) 0+max (-w ()) 0
    constructor <;> apply max_le
    · exact add_le_add (le_max_left _ _) (le_max_left _ _)
    · exact add_nonneg (le_max_right _ _) (le_max_right _ _)
    · linarith [le_max_left (-v ()) 0,le_max_left (-w ()) 0]
    · exact add_nonneg (le_max_right _ _) (le_max_right _ _)
  | succ h ih =>
    have hP : ‖fullPChildren p hp h (v+w)‖ ≤ ‖fullPChildren p hp h v‖+‖fullPChildren p hp h w‖ := by
      refine (lp.norm_mono (p_ne_zero p) (y := fullPChildren p hp h v+fullPChildren p hp h w) ?_).trans (norm_add_le _ _)
      intro i
      simp only [fullPChildren_apply,lp.coeFn_add,Pi.add_apply,Real.norm_eq_abs,
        abs_of_nonneg (fullUpper_nonneg p hp h _).1,
        abs_of_nonneg (add_nonneg (fullUpper_nonneg p hp h _).1 (fullUpper_nonneg p hp h _).1)]
      rw [child_add p hp]
      exact (ih _ _).1
    have hQ : ‖fullQChildren p hp h (v+w)‖ ≤ ‖fullQChildren p hp h v‖+‖fullQChildren p hp h w‖ := by
      refine (lp.norm_mono (p_ne_zero p) (y := fullQChildren p hp h v+fullQChildren p hp h w) ?_).trans (norm_add_le _ _)
      intro i
      simp only [fullQChildren_apply,lp.coeFn_add,Pi.add_apply,Real.norm_eq_abs,
        abs_of_nonneg (fullUpper_nonneg p hp h _).2,
        abs_of_nonneg (add_nonneg (fullUpper_nonneg p hp h _).2 (fullUpper_nonneg p hp h _).2)]
      rw [child_add p hp]
      exact (ih _ _).2
    rw [fullUpper_succ,fullUpper_succ,fullUpper_succ]
    have hm := join_mono (r := v (.inl ())+w (.inl ())) hP hQ
    have ha := join_add (v (.inl ())) (w (.inl ())) ‖fullPChildren p hp h v‖ ‖fullQChildren p hp h v‖
      ‖fullPChildren p hp h w‖ ‖fullQChildren p hp h w‖
    exact ⟨hm.1.trans ha.1,hm.2.trans ha.2⟩

lemma fullUpper_smul_nonneg (h : ℕ) (v : Full p h) (t : ℝ) (ht : 0 ≤ t) :
    fullUpper p hp h (t • v)=t • fullUpper p hp h v := by
  induction h with
  | zero =>
    change (max (t*v ()) 0,max (-(t*v ())) 0)=(t*max (v ()) 0,t*max (-v ()) 0)
    rw [mul_max_of_nonneg _ _ ht,mul_max_of_nonneg _ _ ht,mul_zero,mul_neg]
  | succ h ih =>
    have hP : fullPChildren p hp h (t • v)=t • fullPChildren p hp h v := by
      ext i
      change (fullUpper p hp h (child p hp h (t • v) i)).1=t*(fullUpper p hp h (child p hp h v i)).1
      rw [child_smul,ih]; rfl
    have hQ : fullQChildren p hp h (t • v)=t • fullQChildren p hp h v := by
      ext i
      change (fullUpper p hp h (child p hp h (t • v) i)).2=t*(fullUpper p hp h (child p hp h v i)).2
      rw [child_smul,ih]; rfl
    rw [fullUpper_succ,fullUpper_succ,hP,hQ,norm_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
    exact join_smul _ _ _ _ ht

def fullNu (h : ℕ) (v : Full p h) : ℝ := (fullUpper p hp h v).1+(fullUpper p hp h v).2
lemma fullNu_nonneg (h : ℕ) (v : Full p h) : 0 ≤ fullNu p hp h v :=
  add_nonneg (fullUpper_nonneg p hp h v).1 (fullUpper_nonneg p hp h v).2
@[simp] lemma fullNu_zero (h : ℕ) : fullNu p hp h 0=0 := by simp [fullNu]
lemma fullNu_add (h : ℕ) (v w : Full p h) :
    fullNu p hp h (v+w) ≤ fullNu p hp h v+fullNu p hp h w := by
  have hh := fullUpper_add p hp h v w
  dsimp [fullNu]
  linarith [hh.1,hh.2]
lemma fullNu_neg (h : ℕ) (v : Full p h) : fullNu p hp h (-v)=fullNu p hp h v := by
  simp only [fullNu,fullUpper_neg,add_comm]
lemma fullNu_smul (h : ℕ) (v : Full p h) (t : ℝ) :
    fullNu p hp h (t • v)=|t| * fullNu p hp h v := by
  rcases le_total 0 t with ht|ht
  · simp only [fullNu,fullUpper_smul_nonneg p hp h v t ht,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,abs_of_nonneg ht]
    ring
  · have he : t • v=-((-t) • v) := by module
    rw [he,fullNu_neg]
    simp only [fullNu,fullUpper_smul_nonneg p hp h v (-t) (neg_nonneg.mpr ht),
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul,abs_of_nonpos ht]
    ring

def fullNuSeminorm (h : ℕ) : Seminorm ℝ (Full p h) where
  toFun := fullNu p hp h
  map_zero' := fullNu_zero p hp h
  add_le' := fullNu_add p hp h
  neg' := fullNu_neg p hp h
  smul' t v := by simpa only [Real.norm_eq_abs] using fullNu_smul p hp h v t

lemma fullNu_upper (h : ℕ) (v : Full p h) : fullNu p hp h v ≤ (2*3^h)*‖v‖ := by
  have hh := fullUpper_bound p hp h v
  dsimp [fullNu]
  linarith [hh.1,hh.2]

lemma full_leaf_norm (v : Full p 0) : ‖v‖=|v ()| := by
  have he : v=lp.single p () (v ()) := by ext i; cases i; simp
  rw [he,lp.norm_single (pos_iff_ne_zero.mpr (p_ne_zero p))]
  rfl
lemma rootZero_norm (h : ℕ) (v : Full p (h+1)) (hv : v (.inl ())=0) :
    ‖v‖=‖children p hp h v‖ := by
  rw [lp.norm_eq_tsum_rpow hp,lp.norm_eq_tsum_rpow hp]
  congr 1
  rw [Summable.tsum_sum ((v.property.summable hp).comp_injective Sum.inl_injective)
    ((v.property.summable hp).comp_injective Sum.inr_injective)]
  simp only [hv,norm_zero,Real.zero_rpow (ne_of_gt hp),tsum_zero,zero_add]
  simp_rw [children_apply,child_sum]
  exact (child_summable p hp h v).tsum_prod
lemma root_children_norm (h : ℕ) (v : Full p (h+1)) :
    ‖v‖ ≤ |v (.inl ())|+‖children p hp h v‖ := by
  let r : Full p (h+1) := lp.single p (Sum.inl () : Coord (h+1)) (v (.inl ()))
  have hr : ‖r‖=|v (.inl ())| := lp.norm_single (pos_iff_ne_zero.mpr (p_ne_zero p)) _ _
  have hz : (v-r) (.inl ())=0 := by simp [r]
  have hc : children p hp h (v-r)=children p hp h v := by
    ext i s
    change v (.inr (i,s))-r (.inr (i,s))=v (.inr (i,s))
    simp [r]
  have hh := norm_add_le r (v-r)
  rw [add_sub_cancel,hr,rootZero_norm p hp h (v-r) hz,hc] at hh
  exact hh

lemma fullNu_lower (h : ℕ) (v : Full p h) : ‖v‖ ≤ (h+1:ℝ)*fullNu p hp h v := by
  induction h with
  | zero =>
    rw [full_leaf_norm p]
    norm_num only [Nat.cast_zero,zero_add,one_mul]
    change |v ()| ≤ max (v ()) 0+max (-v ()) 0
    rw [abs_le]; constructor <;> linarith [le_max_left (v ()) 0,le_max_right (v ()) 0,le_max_left (-v ()) 0,le_max_right (-v ()) 0]
  | succ h ih =>
    let P := fullPChildren p hp h v
    let Q := fullQChildren p hp h v
    have hl : ‖children p hp h v‖ ≤ (h+1:ℝ)*‖P+Q‖ := by
      calc
        _ ≤ ‖(h+1:ℝ) • (P+Q)‖ := lp.norm_mono (p_ne_zero p) (fun i => by
          have hh := ih (child p hp h v i)
          change ‖child p hp h v i‖ ≤ ‖(h+1:ℝ)*fullNu p hp h (child p hp h v i)‖
          rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (fullNu_nonneg p hp h _))]
          exact hh)
        _ = _ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ) ≤ h+1)]
    have hchild : ‖children p hp h v‖ ≤ (h+1:ℝ)*fullNu p hp (h+1) v := by
      refine hl.trans ((mul_le_mul_of_nonneg_left (norm_add_le P Q) (by positivity)).trans ?_)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      change ‖P‖+‖Q‖ ≤ (join _ ‖P‖ ‖Q‖).1+(join _ ‖P‖ ‖Q‖).2
      exact add_le_add (le_max_left _ _) (le_max_right _ _)
    have hroot : |v (.inl ())| ≤ fullNu p hp (h+1) v :=
      join_root_bound _ _ _ (norm_nonneg P) (norm_nonneg Q)
    have hh := root_children_norm p hp h v
    push_cast
    nlinarith
end

lemma join_difference (r a b : ℝ) : (join r a b).1-(join r a b).2=r := by
  dsimp [join]
  by_cases h : a ≤ r+b
  · rw [max_eq_right h,max_eq_right (by linarith : a-r ≤ b)]
    ring
  · rw [max_eq_left (le_of_not_ge h),max_eq_left (by linarith : b ≤ a-r)]
    ring
lemma join_least {r a b P Q : ℝ} (hP : a ≤ P) (hQ : b ≤ Q) (hdiff : P-Q=r) :
    (join r a b).1 ≤ P ∧ (join r a b).2 ≤ Q := by
  constructor <;> apply max_le <;> linarith

def fullRoot : (h : ℕ) → Coord h
  | 0 => ()
  | _+1 => Sum.inl ()
variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal)
lemma fullUpper_difference (h : ℕ) (v : Full p h) :
    (fullUpper p hp h v).1-(fullUpper p hp h v).2=v (fullRoot h) := by
  cases h with
  | zero =>
    have hh := join_difference (v ()) 0 0
    simpa only [join,add_zero,zero_sub,max_comm,fullUpper_zero_height,fullRoot] using hh
  | succ h => exact join_difference _ _ _

/-- The complete least upper arrays, including every non-root coordinate. -/
def fullArray : (h : ℕ) → Full p h → Coord h → ℝ × ℝ
  | 0,v,_ => fullUpper p hp 0 v
  | h+1,v,.inl _ => fullUpper p hp (h+1) v
  | h+1,v,.inr (i,s) => fullArray h (child p hp h v i) s
lemma fullArray_root (h : ℕ) (v : Full p h) : fullArray p hp h v (fullRoot h)=fullUpper p hp h v := by
  cases h <;> rfl
lemma fullArray_nonneg_diff (h : ℕ) (v : Full p h) (s : Coord h) :
    0 ≤ (fullArray p hp h v s).1 ∧ 0 ≤ (fullArray p hp h v s).2 ∧
      (fullArray p hp h v s).1-(fullArray p hp h v s).2=v s := by
  induction h with
  | zero => exact ⟨(fullUpper_nonneg p hp 0 v).1,(fullUpper_nonneg p hp 0 v).2,fullUpper_difference p hp 0 v⟩
  | succ h ih =>
    cases s with
    | inl u => exact ⟨(fullUpper_nonneg p hp (h+1) v).1,(fullUpper_nonneg p hp (h+1) v).2,fullUpper_difference p hp (h+1) v⟩
    | inr q => exact ih (child p hp h v q.1) q.2

/-- Exact upper-array constraints: nonnegative values, coordinate difference v,
    and each of the two arrays dominating the countable ℓp norm of its children.
    At leaves the child norm is zero. -/
def FullAdmissible : (h : ℕ) → Full p h → (Coord h → ℝ × ℝ) → Prop
  | 0,v,A => 0 ≤ (A ()).1 ∧ 0 ≤ (A ()).2 ∧ (A ()).1-(A ()).2=v ()
  | h+1,v,A =>
    (0 ≤ (A (.inl ())).1 ∧ 0 ≤ (A (.inl ())).2 ∧ (A (.inl ())).1-(A (.inl ())).2=v (.inl ())) ∧
    (∃ a b : lp (fun _ : ℕ => ℝ) p,
      (∀ i,a i=(A (.inr (i,fullRoot h))).1) ∧ (∀ i,b i=(A (.inr (i,fullRoot h))).2) ∧
      ‖a‖ ≤ (A (.inl ())).1 ∧ ‖b‖ ≤ (A (.inl ())).2) ∧
    ∀ i,FullAdmissible h (child p hp h v i) (fun s => A (.inr (i,s)))
lemma fullAdmissible_root (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) (h : ℕ) {v : Full p h} {A : Coord h → ℝ × ℝ}
    (hA : FullAdmissible p hp h v A) :
    0 ≤ (A (fullRoot h)).1 ∧ 0 ≤ (A (fullRoot h)).2 ∧
      (A (fullRoot h)).1-(A (fullRoot h)).2=v (fullRoot h) := by
  cases h with
  | zero => exact hA
  | succ h => exact hA.1
lemma fullArray_admissible (h : ℕ) (v : Full p h) :
    FullAdmissible p hp h v (fullArray p hp h v) := by
  induction h with
  | zero => exact fullArray_nonneg_diff p hp 0 v ()
  | succ h ih =>
    refine ⟨fullArray_nonneg_diff p hp (h+1) v (.inl ()),?_,fun i => ih (child p hp h v i)⟩
    refine ⟨fullPChildren p hp h v,fullQChildren p hp h v,?_,?_,le_max_left _ _,le_max_right _ _⟩
    · intro i
      change (fullUpper p hp h (child p hp h v i)).1=(fullArray p hp h (child p hp h v i) (fullRoot h)).1
      rw [fullArray_root]
    · intro i
      change (fullUpper p hp h (child p hp h v i)).2=(fullArray p hp h (child p hp h v i) (fullRoot h)).2
      rw [fullArray_root]
lemma fullUpper_least (h : ℕ) {v : Full p h} {A : Coord h → ℝ × ℝ}
    (hA : FullAdmissible p hp h v A) :
    (fullUpper p hp h v).1 ≤ (A (fullRoot h)).1 ∧
    (fullUpper p hp h v).2 ≤ (A (fullRoot h)).2 := by
  induction h with
  | zero =>
    have hn := fullAdmissible_root p hp 0 hA
    change max (v ()) 0 ≤ (A ()).1 ∧ max (-v ()) 0 ≤ (A ()).2
    constructor <;> apply max_le <;> linarith [hn.1,hn.2.1,hn.2.2]
  | succ h ih =>
    obtain ⟨hr,⟨a,b,ha,hb,hna,hnb⟩,hc⟩ := hA
    have hP : ‖fullPChildren p hp h v‖ ≤ ‖a‖ := by
      apply lp.norm_mono (p_ne_zero p)
      intro i
      rw [fullPChildren_apply,Real.norm_eq_abs,abs_of_nonneg (fullUpper_nonneg p hp h _).1,
        ha i,Real.norm_eq_abs,abs_of_nonneg (fullAdmissible_root p hp h (hc i)).1]
      exact (ih (hc i)).1
    have hQ : ‖fullQChildren p hp h v‖ ≤ ‖b‖ := by
      apply lp.norm_mono (p_ne_zero p)
      intro i
      rw [fullQChildren_apply,Real.norm_eq_abs,abs_of_nonneg (fullUpper_nonneg p hp h _).2,
        hb i,Real.norm_eq_abs,abs_of_nonneg (fullAdmissible_root p hp h (hc i)).2.1]
      exact (ih (hc i)).2
    exact join_least (hP.trans hna) (hQ.trans hnb) hr.2.2
lemma fullArray_least (h : ℕ) {v : Full p h} {A : Coord h → ℝ × ℝ}
    (hA : FullAdmissible p hp h v A) (s : Coord h) :
    (fullArray p hp h v s).1 ≤ (A s).1 ∧ (fullArray p hp h v s).2 ≤ (A s).2 := by
  induction h with
  | zero => exact fullUpper_least p hp 0 hA
  | succ h ih =>
    cases s with
    | inl u => exact fullUpper_least p hp (h+1) hA
    | inr q => exact ih (hA.2.2 q.1) q.2
end RecursiveModel

namespace Midpoint
namespace Heads
variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
def transport (H : Heads ι E) (e : E ≃ₗᵢ[ℝ] F) : Heads ι F where
  projection i := e.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((H.projection i).comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  idempotent i x := by
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv,LinearIsometryEquiv.symm_apply_apply,H.idempotent]
  finite i := by
    let P := H.projection i
    let e' := e.toLinearEquiv.toLinearMap
    let Q : F →ₗ[ℝ] F := e'.comp (P.toLinearMap.comp e.symm.toLinearEquiv.toLinearMap)
    have : FiniteDimensional ℝ (LinearMap.range P.toLinearMap) := H.finite i
    have : FiniteDimensional ℝ ((LinearMap.range P.toLinearMap).map e') := Module.Finite.map _ _
    change FiniteDimensional ℝ (LinearMap.range Q)
    apply Submodule.finiteDimensional_of_le (S₂ := (LinearMap.range P.toLinearMap).map e')
    rintro y ⟨x,rfl⟩
    exact ⟨P (e.symm x),⟨e.symm x,rfl⟩,rfl⟩
  approximation x η hη := by
    obtain ⟨i,p,hp,hclose⟩ := H.approximation (e.symm x) η hη
    refine ⟨i,e p,?_,?_⟩
    · simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv,LinearIsometryEquiv.symm_apply_apply,hp]
    · have he : x-e p=e (e.symm x-p) := by simp
      rw [he,e.norm_map]
      exact hclose
lemma transport_projection (H : Heads ι E) (e : E ≃ₗᵢ[ℝ] F) (i : ι) (x : F) :
    (H.transport e).projection i x=e (H.projection i (e.symm x)) := rfl
end Heads

end Midpoint

namespace RecursiveModel
lemma exponent_ne_top (h : ℕ) : exponent h ≠ ⊤ := by
  simp only [exponent,ne_eq,ENNReal.add_eq_top,ENNReal.one_ne_top,ENNReal.inv_eq_top,false_or]
  positivity
lemma exponent_real_pos (h : ℕ) : 0 < (exponent h).toReal :=
  ENNReal.toReal_pos (p_ne_zero (exponent h)) (exponent_ne_top h)
def fullData (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) (h : ℕ) : EquivalentNorm.Data (Full p h) where
  seminorm := fullNuSeminorm p hp h
  lowerConstant := h+1
  upperConstant := 2*3^h
  lower := fullNu_lower p hp h
  upper := fullNu_upper p hp h
abbrev VectorComponent (h : ℕ) := (fullData (exponent h) (exponent_real_pos h) (h+1)).Space

abbrev FullVectorSpace := lp VectorComponent 2

def fullVectorEmbedding : ForestVec →ₗ[ℝ] FullVectorSpace :=
  outerEmbedding (fun h => (fullData (exponent h) (exponent_real_pos h) (h+1)).coordinateEmbedding)
lemma fullVectorEmbedding_norm (v : ForestVec) : ‖fullVectorEmbedding v‖=vectorSeminorm v := by
  change ‖fullVectorEmbedding v‖=‖finiteLp 2 (vectorNormValues v)‖
  have he (h : ℕ) : ‖fullVectorEmbedding v h‖=‖finiteLp 2 (vectorNormValues v) h‖ := by
    change fullNu (exponent h) (exponent_real_pos h) (h+1) (finiteLp (exponent h) (components v h))=|nu (exponent h) (h+1) (components v h)|
    rw [abs_of_nonneg (nu_nonneg _ _ _)]
    unfold fullNu nu
    rw [fullUpper_finiteLp]
  exact le_antisymm (lp.norm_mono (by norm_num) (fun h => (he h).le))
    (lp.norm_mono (by norm_num) (fun h => (he h).ge))
lemma fullVectorEmbedding_dense : DenseRange fullVectorEmbedding :=
  outerEmbedding_dense _ (fun h => (fullData (exponent h) (exponent_real_pos h) (h+1)).coordinateEmbedding_dense (exponent_ne_top h))
/-- Exact full-model identification, preserving every finite coordinate. -/
def fullVectorEquiv : VectorSpace ≃ₗᵢ[ℝ] FullVectorSpace :=
  vectorData.completionEquiv fullVectorEmbedding fullVectorEmbedding_norm fullVectorEmbedding_dense
lemma fullVectorEquiv_embedding (v : ForestVec) :
    fullVectorEquiv (vectorData.embedding v)=fullVectorEmbedding v := vectorData.completionMap_coe _ _ _
def fullVectorHeads : Midpoint.Heads ForestHead FullVectorSpace := vectorHeads.transport fullVectorEquiv
open RecursiveApplications
theorem full_sixth_graph (hinput : SixthInput fullVectorHeads) {D s : ℝ} (k : ℕ)
    (f : Diamond.Vertex k → FullVectorSpace) (hf : Diamond.HasDistortion k f D s) :
    D⁻¹ ≤ (q6 D⁻¹)^k := sixth_depth fullVectorHeads hinput k f hf
theorem full_cubic_graph (hinput : CubicInput fullVectorHeads) {D s : ℝ} (k : ℕ)
    (f : Diamond.Vertex k → FullVectorSpace) (hf : Diamond.HasDistortion k f D s) :
    1 ≤ D*(theta D⁻¹)^k := cubic_depth fullVectorHeads hinput k f hf
end RecursiveModel

end DiamondDistortion

end

end OAI
