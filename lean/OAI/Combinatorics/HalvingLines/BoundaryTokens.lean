import OAI.Combinatorics.HalvingLines.Enhancement

namespace OAI

open Filter Topology

namespace PlanarHalving.Boundary
open Set
open scoped Classical

lemma monotone_pred_changes {m : ℕ} (p : Fin (m+1) → Prop)
    (hp : ∀ i j, i≤j → p i → p j) :
    (Finset.univ.filter fun i : Fin m => ¬ (p i.castSucc ↔ p i.succ)).card≤1 := by
  classical
  have hstep {i : Fin m} (hi : ¬ (p i.castSucc ↔ p i.succ)) : ¬p i.castSucc ∧ p i.succ := by
    have hf := hp i.castSucc i.succ (by simp [Fin.le_def])
    tauto
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hi' := hstep (Finset.mem_filter.mp hi).2
  have hj' := hstep (Finset.mem_filter.mp hj).2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact hj'.1 (hp i.succ j.castSucc (by simp only [Fin.le_def,Fin.lt_def,Fin.val_succ,Fin.val_castSucc] at *; omega) hi'.2)
  · exact hi'.1 (hp j.succ i.castSucc (by simp only [Fin.le_def,Fin.lt_def,Fin.val_succ,Fin.val_castSucc] at *; omega) hj'.2)

def InSquare (a b : ℝ) (x : Point) : Prop := a<x.1 ∧ x.1<b ∧ a<x.2 ∧ x.2<b

lemma monotone_square_changes {m : ℕ} (f : Fin (m+1) → Point)
    (h1 : Monotone (fun i => (f i).1)) (h2 : Monotone (fun i => (f i).2))
    (a b : ℝ) :
    (Finset.univ.filter fun i : Fin m => ¬ (InSquare a b (f i.castSucc) ↔ InSquare a b (f i.succ))).card≤4 := by
  classical
  let A := Finset.univ.filter fun i : Fin m => ¬ (a<(f i.castSucc).1 ↔ a<(f i.succ).1)
  let B := Finset.univ.filter fun i : Fin m => ¬ (b≤(f i.castSucc).1 ↔ b≤(f i.succ).1)
  let C := Finset.univ.filter fun i : Fin m => ¬ (a<(f i.castSucc).2 ↔ a<(f i.succ).2)
  let D := Finset.univ.filter fun i : Fin m => ¬ (b≤(f i.castSucc).2 ↔ b≤(f i.succ).2)
  have hA : A.card≤1 := monotone_pred_changes (fun i => a<(f i).1) (fun i j hij ha => ha.trans_le (h1 hij))
  have hB : B.card≤1 := monotone_pred_changes (fun i => b≤(f i).1) (fun i j hij ha => ha.trans (h1 hij))
  have hC : C.card≤1 := monotone_pred_changes (fun i => a<(f i).2) (fun i j hij ha => ha.trans_le (h2 hij))
  have hD : D.card≤1 := monotone_pred_changes (fun i => b≤(f i).2) (fun i j hij ha => ha.trans (h2 hij))
  have hs : (Finset.univ.filter fun i : Fin m =>
      ¬ (InSquare a b (f i.castSucc) ↔ InSquare a b (f i.succ)))⊆ A∪B∪C∪D := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    simp only [A,B,C,D,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
    dsimp only [InSquare] at hi'
    simp only [lt_iff_not_ge] at *
    tauto
  have ht := Finset.card_le_card hs
  have h4 := Finset.card_union_le (A∪B∪C) D
  have h3 := Finset.card_union_le (A∪B) C
  have h2 := Finset.card_union_le A B
  omega

lemma square_token_budget {τ : Type*} [Fintype τ] {m : ℕ}
    (f : Fin (m+1) → τ → Point)
    (h1 : ∀ u, Monotone (fun i => (f i u).1))
    (h2 : ∀ u, Monotone (fun i => (f i u).2)) (a b : ℝ) :
    (∑ i : Fin m, (Finset.univ.filter fun u : τ =>
      ¬ (InSquare a b (f i.castSucc u) ↔ InSquare a b (f i.succ u))).card)≤4*Fintype.card τ := by
  classical
  have he : (∑ i : Fin m, (Finset.univ.filter fun u : τ =>
      ¬ (InSquare a b (f i.castSucc u) ↔ InSquare a b (f i.succ u))).card)=
      ∑ u : τ, (Finset.univ.filter fun i : Fin m =>
      ¬ (InSquare a b (f i.castSucc u) ↔ InSquare a b (f i.succ u))).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [he]
  calc
    _ ≤ ∑ _u : τ, 4 := Finset.sum_le_sum (fun u _ => monotone_square_changes (fun i => f i u) (h1 u) (h2 u) a b)
    _ = _ := by simp [Nat.mul_comm]

end PlanarHalving.Boundary

namespace PlanarHalving.Boundary
open Set
open scoped Classical

noncomputable def rawNormal (t : ℝ) : Point := (-t,1-t)
noncomputable def frameWeight (a b l u s : ℝ) : ℝ := a*(s-l)+b*(u-s)
noncomputable def frameParameter (a b l u s : ℝ) : ℝ := a*(s-l)/frameWeight a b l u s

lemma frameWeight_pos {a b l u s : ℝ} (ha : 0<a) (hb : 0<b)
    (hlu : l<u) (hs : s∈Icc l u) : 0<frameWeight a b l u s := by
  have h1 := mul_nonneg ha.le (sub_nonneg.mpr hs.1)
  have h2 := mul_nonneg hb.le (sub_nonneg.mpr hs.2)
  rcases lt_or_eq_of_le hs.1 with h | h
  · exact add_pos_of_pos_of_nonneg (mul_pos ha (sub_pos.mpr h)) h2
  · subst s; simpa [frameWeight] using mul_pos hb (sub_pos.mpr hlu)

lemma frameParameter_mem {a b l u s : ℝ} (ha : 0<a) (hb : 0<b)
    (hlu : l<u) (hs : s∈Icc l u) : frameParameter a b l u s∈Icc (0:ℝ) 1 := by
  have hd := frameWeight_pos ha hb hlu hs
  constructor
  · exact div_nonneg (mul_nonneg ha.le (sub_nonneg.mpr hs.1)) hd.le
  · apply (div_le_one hd).mpr
    dsimp [frameWeight]
    linarith [mul_nonneg hb.le (sub_nonneg.mpr hs.2)]

lemma frameParameter_monotone {a b l u : ℝ} (ha : 0<a) (hb : 0<b) (hlu : l<u) :
    MonotoneOn (frameParameter a b l u) (Icc l u) := by
  intro s hs t ht hst
  apply (div_le_div_iff₀ (frameWeight_pos ha hb hlu hs) (frameWeight_pos ha hb hlu ht)).mpr
  dsimp [frameWeight]
  have hp := mul_nonneg (mul_nonneg ha.le hb.le) (mul_nonneg (sub_nonneg.mpr hlu.le) (sub_nonneg.mpr hst))
  nlinarith only [hp]

lemma frame_apply (E : Point ≃L[ℝ] Point) {a b l u : ℝ}
    (h1 : E (1,0)=a • (1,l)) (h2 : E (0,1)=b • (1,u)) (x : Point) :
    E x=(a*x.1+b*x.2,a*l*x.1+b*u*x.2) := by
  have hx : x=x.1 • ((1,0):Point)+x.2 • ((0,1):Point) := by ext <;> simp
  conv_lhs => rw [hx,map_add,map_smul,map_smul,h1,h2]
  ext <;> dsimp <;> ring

lemma frame_projection (E : Point ≃L[ℝ] Point) {a b l u s : ℝ}
    (h1 : E (1,0)=a • (1,l)) (h2 : E (0,1)=b • (1,u))
    (hd : frameWeight a b l u s≠0) (x : Point) :
    Sweep.projection s (E x)=frameWeight a b l u s * dot (rawNormal (frameParameter a b l u s)) x := by
  rw [frame_apply E h1 h2]
  dsimp [Sweep.projection,dot,rawNormal,frameParameter]
  field_simp
  dsimp [frameWeight]
  ring

lemma frame_inverse_nonneg (E : Point ≃L[ℝ] Point) {a b l u : ℝ}
    (ha : 0<a) (hb : 0<b) (hlu : l<u)
    (h1 : E (1,0)=a • (1,l)) (h2 : E (0,1)=b • (1,u))
    (v : Point) (hlo : l*v.1≤v.2) (hhi : v.2≤u*v.1) :
    0≤(E.symm v).1 ∧ 0≤(E.symm v).2 := by
  have he := frame_apply E h1 h2 (E.symm v)
  rw [E.apply_symm_apply] at he
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  change v.1=a*(E.symm v).1+b*(E.symm v).2 at he1
  change v.2=a*l*(E.symm v).1+b*u*(E.symm v).2 at he2
  rw [he1,he2] at hlo hhi
  constructor
  · have hp : 0<a*(u-l) := mul_pos ha (sub_pos.mpr hlu)
    have hh : 0≤a*(u-l)*(E.symm v).1 := by nlinarith [hhi]
    exact (mul_nonneg_iff_of_pos_left hp).mp hh
  · have hp : 0<b*(u-l) := mul_pos hb (sub_pos.mpr hlu)
    have hh : 0≤b*(u-l)*(E.symm v).2 := by nlinarith [hlo]
    exact (mul_nonneg_iff_of_pos_left hp).mp hh

lemma rawNormal_bounds (t : ℝ) : (1:ℝ)/2 ≤ sqNorm (rawNormal t) := by
  dsimp [sqNorm,rawNormal]
  nlinarith [sq_nonneg (t-1/2)]
lemma rawNormal_difference (s t : ℝ) : sqNorm (rawNormal s-rawNormal t)=2*(s-t)^2 := by
  dsimp [sqNorm,rawNormal]; ring

lemma separating_threshold {V : Type*} [Fintype V] (f : V → ℝ) (M : Finset V)
    (hsep : ∀ i∈M, ∀ j∉M, f i<f j) : ∃ c : ℝ, ∀ i, i∈M ↔ f i<c := by
  classical
  by_cases hM : M.Nonempty
  · obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image M f hM
    by_cases hN : (Finset.univ\M).Nonempty
    · obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image (Finset.univ\M) f hN
      have hn := (Finset.mem_sdiff.mp hj).2
      obtain ⟨c,hc,hd⟩ := exists_between (hsep i hi j hn)
      refine ⟨c,fun v => ⟨fun hv => (hmax v hv).trans_lt hc,fun hv => ?_⟩⟩
      by_contra hvM
      exact (not_lt_of_ge ((hmin v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hvM⟩)).trans' hd.le)) hv
    · refine ⟨f i+1,fun v => ⟨fun hv => by linarith [hmax v hv],fun _ => ?_⟩⟩
      by_contra hv
      exact hN ⟨v,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hv⟩⟩
  · have he : M=∅ := Finset.not_nonempty_iff_eq_empty.mp hM
    subst M
    by_cases hn : Nonempty V
    · let := hn
      obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
      refine ⟨f j-1,fun v => ?_⟩
      simp only [Finset.notMem_empty,false_iff,not_lt]
      linarith [hmin v (Finset.mem_univ _)]
    · exact ⟨0,fun v => (hn ⟨v⟩).elim⟩

end PlanarHalving.Boundary

namespace PlanarHalving.Boundary
open Set
open scoped Classical

noncomputable def physical (E : Point ≃L[ℝ] Point) (o : Point) (r : ℝ) (p : Point) : Point :=
  r • E.symm (p-o)

lemma physical_sub (E : Point ≃L[ℝ] Point) (o : Point) (r : ℝ) (p q : Point) :
    physical E o r q - physical E o r p=r • E.symm (q-p) := by
  rw [physical,physical,← smul_sub,← map_sub]
  congr 2
  abel

lemma physical_injective (E : Point ≃L[ℝ] Point) (o : Point) {r : ℝ} (hr : r≠0) :
    Function.Injective (physical E o r) := by
  intro p q h
  have he := (smul_right_injective Point hr) h
  simpa only [sub_add_cancel] using congrArg (fun x : Point => x+o) (E.symm.injective he)

lemma projection_physical (E : Point ≃L[ℝ] Point) {a b l u s : ℝ}
    (h1 : E (1,0)=a • (1,l)) (h2 : E (0,1)=b • (1,u))
    (hd : frameWeight a b l u s≠0) (o : Point) (r : ℝ) (p : Point) :
    dot (rawNormal (frameParameter a b l u s)) (physical E o r p)=
      r/frameWeight a b l u s*(Sweep.projection s p-Sweep.projection s o) := by
  have he := frame_projection E h1 h2 hd (E.symm (p-o))
  rw [E.apply_symm_apply] at he
  calc
    _ = r*dot (rawNormal (frameParameter a b l u s)) (E.symm (p-o)) := by dsimp [physical,dot]; ring
    _ = r/frameWeight a b l u s*(frameWeight a b l u s*dot (rawNormal (frameParameter a b l u s)) (E.symm (p-o))) := by field_simp
    _ = _ := by rw [← he]; dsimp [Sweep.projection]; congr 1; ring

lemma actual_transformed_cuts {n R k a₀ : ℕ} {P : Fin n → Point}
    (S : @Batches.System n R k a₀ P) (E : Point ≃L[ℝ] Point)
    {a b l u : ℝ} (ha : 0<a) (hb : 0<b) (hlu : l<u)
    (h1 : E (1,0)=a • (1,l)) (h2 : E (0,1)=b • (1,u))
    (hspan : ∀ i, S.slope i∈Icc l u) (o : Point) {r : ℝ} (hr : 0<r) :
    ∃ c : Fin (R+1) → ℝ, ∀ i v,
      v∈S.marks i ↔ dot (rawNormal (frameParameter a b l u (S.slope i))) (physical E o r (P v))<c i := by
  choose c hc using fun i => separating_threshold
    (fun v => dot (rawNormal (frameParameter a b l u (S.slope i))) (physical E o r (P v)))
    (S.marks i) (by
      intro v hv w hw
      rw [projection_physical E h1 h2 (frameWeight_pos ha hb hlu (hspan i)).ne' o r,
        projection_physical E h1 h2 (frameWeight_pos ha hb hlu (hspan i)).ne' o r]
      exact mul_lt_mul_of_pos_left (sub_lt_sub_right (S.separates i v hv w hw) _)
        (div_pos hr (frameWeight_pos ha hb hlu (hspan i))))
  exact ⟨c,hc⟩

lemma actual_tokens_monotone {n R k a₀ : ℕ} {P : Fin n → Point} [NeZero a₀]
    (S : @Batches.System n R k a₀ P) (E : Point ≃L[ℝ] Point)
    {a b l u : ℝ} (ha : 0<a) (hb : 0<b) (hlu : l<u)
    (h1 : E (1,0)=a • (1,l)) (h2 : E (0,1)=b • (1,u))
    (hspan : ∀ i, S.slope i∈Icc l u) (o : Point) {r : ℝ} (hr : 0<r)
    (j : Fin a₀) (v : ↥(S.marks 0)) :
    Monotone (fun i => (physical E o r (P (S.tokenState j i v))).1) ∧
      Monotone (fun i => (physical E o r (P (S.tokenState j i v))).2) := by
  have hstep (i : Fin R) :
      0 ≤ (physical E o r (P (S.tokenState j i.succ v))-
        physical E o r (P (S.tokenState j i.castSucc v))).1 ∧
      0 ≤ (physical E o r (P (S.tokenState j i.succ v))-
        physical E o r (P (S.tokenState j i.castSucc v))).2 := by
    rcases S.token_step j v i with he | ⟨hl,hg⟩
    · rw [he,sub_self]; exact ⟨le_rfl,le_rfl⟩
    · have hx := sub_pos.mpr (S.edge_right i hl hg)
      have hs := S.edge_slope i hl hg
      have hlo : l*(P (S.tokenState j i.succ v)-P (S.tokenState j i.castSucc v)).1 ≤
          (P (S.tokenState j i.succ v)-P (S.tokenState j i.castSucc v)).2 :=
        (le_div_iff₀ hx).mp ((hspan i.castSucc).1.trans hs.1.le)
      have hhi : (P (S.tokenState j i.succ v)-P (S.tokenState j i.castSucc v)).2 ≤
          u*(P (S.tokenState j i.succ v)-P (S.tokenState j i.castSucc v)).1 :=
        (div_le_iff₀ hx).mp (hs.2.le.trans (hspan i.succ).2)
      have hh := frame_inverse_nonneg E ha hb hlu h1 h2 _ hlo hhi
      rw [physical_sub]
      exact ⟨mul_nonneg hr.le hh.1,mul_nonneg hr.le hh.2⟩
  constructor
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact sub_nonneg.mp (hstep i).1
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact sub_nonneg.mp (hstep i).2

end PlanarHalving.Boundary

namespace PlanarHalving.Boundary
open Set
open scoped Classical

noncomputable def clipCut (c : ℝ) : ℝ := max (-4) (min 4 c)
lemma clipCut_mem (c : ℝ) : clipCut c∈Icc (-4:ℝ) 4 := by
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
lemma clipCut_distance {t : ℝ} (ht : t∈Icc (-4:ℝ) 4) (c : ℝ) :
    |t-clipCut c|≤|t-c| := by
  obtain ⟨htlo,hthi⟩ := ht
  by_cases hc : c≤-4
  · rw [clipCut,min_eq_right (hc.trans (by norm_num)),max_eq_left hc,
      abs_of_nonneg (by linarith : 0≤t-(-4)),abs_of_nonneg (by linarith : 0≤t-c)]
    linarith
  · by_cases hd : 4≤c
    · rw [clipCut,min_eq_left hd,max_eq_right (by norm_num : (-4:ℝ)≤4),
        abs_of_nonpos (by linarith : t-4≤0),abs_of_nonpos (by linarith : t-c≤0)]
      linarith
    · rw [clipCut,min_eq_right (le_of_not_ge hd),max_eq_right (le_of_not_ge hc)]

lemma rawNormal_dot_bound {t : ℝ} (ht : t∈Icc (0:ℝ) 1) {x : Point}
    (hx : InSquare (-2) 2 x) : |dot (rawNormal t) x|≤2 := by
  have htlo := ht.1
  have hthi := ht.2
  have h1 : |x.1|≤2 := abs_le.mpr ⟨hx.1.le,hx.2.1.le⟩
  have h2 : |x.2|≤2 := abs_le.mpr ⟨hx.2.2.1.le,hx.2.2.2.le⟩
  calc
    _ ≤ |(-t)*x.1|+|(1-t)*x.2| := abs_add_le _ _
    _ = t*|x.1|+(1-t)*|x.2| := by rw [abs_mul,abs_mul,abs_neg,abs_of_nonneg ht.1,abs_of_nonneg (by linarith : 0≤1-t)]
    _ ≤ t*2+(1-t)*2 := add_le_add (mul_le_mul_of_nonneg_left h1 ht.1) (mul_le_mul_of_nonneg_left h2 (by linarith))
    _ = 2 := by ring

lemma finite_raw_bound {V τ : Type*} [Fintype V] [Fintype τ]
    {m : ℕ} (p : V → Point) (f : Fin (m+1) → τ → V)
    (hf : ∀ i, Function.Injective (f i)) (A : Finset V)
    (t c : Fin (m+1) → ℝ) (ht : Monotone t) (htI : ∀ i, t i∈Icc (0:ℝ) 1)
    (hcut : ∀ i v, v∈Finset.univ.image (f i) ↔ dot (rawNormal (t i)) (p v)<c i)
    (hactive : ∀ v∈A, ∃ i j : Fin (m+1), ¬(v∈Finset.univ.image (f i) ↔ v∈Finset.univ.image (f j))) :
    ∃ d : Fin 3 → ℝ, (∀ j, d j∈Icc (-4:ℝ) 4) ∧
      (A.filter fun v => InSquare (-2) 2 (p v) ∧
        ∀ j, 18*(t (Fin.last m)-t 0)< |dot (rawNormal (t 0)) (p v)-d j|).card≤
      2*∑ i : Fin m, (Finset.univ.filter fun u : τ =>
        ¬(InSquare (-2) 2 (p (f i.castSucc u)) ↔ InSquare (-2) 2 (p (f i.succ u)))).card := by
  classical
  obtain ⟨imin,hmin⟩ := Finite.exists_min c
  obtain ⟨imax,hmax⟩ := Finite.exists_max c
  let d : Fin 3 → ℝ := ![clipCut (c 0),clipCut (c imin),clipCut (c imax)]
  refine ⟨d,fun j => by fin_cases j <;> exact clipCut_mem _,?_⟩
  let B := Finset.univ.filter fun v => InSquare (-2) 2 (p v)
  let θ := t (Fin.last m)-t 0
  have hθ : 0≤θ := sub_nonneg.mpr (ht (Fin.zero_le _))
  let g : ℕ → τ → V := fun i => f ⟨min i m,by omega⟩
  have hg (i : Fin (m+1)) : g i=f i := by
    have he : (⟨min i.val m,by omega⟩ : Fin (m+1))=i := Fin.ext (min_eq_left (by omega))
    exact congrArg f he
  have hgzero : g 0=f 0 := hg 0
  have hnormal (i : Fin (m+1)) : sqNorm (rawNormal (t i)-rawNormal (t 0))≤(2*θ)^2 := by
    rw [rawNormal_difference]
    have h0 := ht (Fin.zero_le i)
    have h1 := ht (Fin.le_last i)
    have hh : (t i-t 0)^2≤θ^2 := pow_le_pow_left₀ (sub_nonneg.mpr h0) (by dsimp [θ]; linarith) 2
    nlinarith [sq_nonneg θ]
  have herr (i : Fin (m+1)) (v : V) (hv : v∈B) :
      |dot (rawNormal (t i)-rawNormal (t 0)) (p v)|≤3*(2*θ) := by
    apply abs_dot_le (by norm_num) (by positivity) (hnormal i)
    have hv' := (Finset.mem_filter.mp hv).2
    have h1 : |(p v).1|≤2 := abs_le.mpr ⟨hv'.1.le,hv'.2.1.le⟩
    have h2 : |(p v).2|≤2 := abs_le.mpr ⟨hv'.2.2.1.le,hv'.2.2.2.le⟩
    have h1' := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤2)).mpr h1
    have h2' := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤2)).mpr h2
    simp only [sq_abs] at h1' h2'
    dsimp [sqNorm]; nlinarith
  have hmain := three_strips_tokens m g (fun i hi => hf _) A B
    (fun v => dot (rawNormal (t 0)) (p v)) c
    (fun i v => dot (rawNormal (t i)-rawNormal (t 0)) (p v)) imin imax (3*(2*θ))
    (by positivity) hmin hmax herr (fun v _ => by simp [dot])
    (by
      intro i v _
      rw [hg]
      have he : dot (rawNormal (t 0)) (p v)+dot (rawNormal (t i)-rawNormal (t 0)) (p v)=dot (rawNormal (t i)) (p v) := by dsimp [dot]; ring
      rw [he]
      exact hcut i v)
    (by
      intro v hv
      have hh := changes_initial (fun i : Fin (m+1) => v∈Finset.univ.image (f i)) 0 (hactive v hv)
      simpa only [hgzero,hg] using hh)
  have hs : (A.filter fun v => InSquare (-2) 2 (p v) ∧
      ∀ j,18*θ< |dot (rawNormal (t 0)) (p v)-d j|)⊆
      ((A∩B).filter fun v => ¬(|dot (rawNormal (t 0)) (p v)-c 0|≤3*(3*(2*θ)) ∨
        |dot (rawNormal (t 0)) (p v)-c imin|≤3*(3*(2*θ)) ∨
        |dot (rawNormal (t 0)) (p v)-c imax|≤3*(3*(2*θ)))) := by
    intro v hv
    obtain ⟨hvA,hvB,hvD⟩ := Finset.mem_filter.mp hv
    refine Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hvA,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvB⟩⟩,?_⟩
    have hvdot := abs_le.mp (rawNormal_dot_bound (htI 0) hvB)
    have hd (c : ℝ) := clipCut_distance (show dot (rawNormal (t 0)) (p v)∈Icc (-4:ℝ) 4 by constructor <;> linarith) c
    have h0 := (hvD 0).trans_le (hd (c 0))
    have h1 := (hvD 1).trans_le (hd (c imin))
    have h2 := (hvD 2).trans_le (hd (c imax))
    change 18*θ< |dot (rawNormal (t 0)) (p v)-c 0| at h0
    change 18*θ< |dot (rawNormal (t 0)) (p v)-c imin| at h1
    change 18*θ< |dot (rawNormal (t 0)) (p v)-c imax| at h2
    rintro (hh|hh|hh) <;> linarith
  apply (Finset.card_le_card hs).trans
  convert hmain using 1
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ext u
  have hgi := hg i.castSucc
  have hgj := hg i.succ
  simp only [Fin.val_castSucc,Fin.val_succ] at hgi hgj
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,hgi,hgj,B]

end PlanarHalving.Boundary

namespace PlanarHalving.Spatial
open Set Metric MeasureTheory Boundary
open scoped ENNReal

lemma strip_bound_of_disk_nonneg (μ : Measure Point) {C d : ℝ} (hC : 0 ≤ C) (hd : 1 < d)
    (hbound : ∀ x : Point, ∀ r : ℝ, 0 < r → μ (closedBall x r) ≤ ENNReal.ofReal (C*r^d))
    (ν : Point) (hν : sqNorm ν=1) (c : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    μ (closedBall (0:Point) 1 ∩ {x | |dot ν x-c| ≤ r}) ≤
      ENNReal.ofReal (13*C*(1+3^d)*r^(d-1)) := by
  rcases hr.eq_or_lt with he | hr
  · subst r
    have hz := line_null_of_disk μ hC hd hbound ν hν c
    have heq : {x : Point | |dot ν x-c| ≤ 0}={x | dot ν x=c} := by ext x; simp [sub_eq_zero]
    rw [heq,hz]
    exact zero_le
  · by_cases h1 : r ≤ 1
    · apply (strip_bound_of_disk μ hC hbound ν hν c hr h1).trans
      apply ENNReal.ofReal_le_ofReal
      gcongr
      linarith
    · have h1' : 1 ≤ r := (not_le.mp h1).le
      have hp : 1 ≤ r^(d-1) := Real.one_le_rpow h1' (by linarith)
      calc
        _  ≤  μ (closedBall (0:Point) 1) := measure_mono inter_subset_left
        _  ≤  ENNReal.ofReal C := by simpa using hbound 0 1 (by norm_num)
        _  ≤  _ := by
          apply ENNReal.ofReal_le_ofReal
          have h3 : 0 ≤ (3:ℝ)^d := Real.rpow_nonneg (by norm_num) _
          have hh : C ≤ 13*C*(1+3^d) := by nlinarith
          exact hh.trans (le_mul_of_one_le_right (by positivity) hp)

lemma normalize_sqNorm (ν : Point) (hν : 0 < sqNorm ν) :
    sqNorm ((Real.sqrt (sqNorm ν))⁻¹ • ν)=1 := by
  have hs := Real.sq_sqrt hν.le
  have hn := (Real.sqrt_pos.mpr hν).ne'
  dsimp [sqNorm] at *
  field_simp
  nlinarith only [hs]

lemma raw_strip_bound (μ : Measure Point) {C d : ℝ} (hC : 0 ≤ C) (hd : 1 < d)
    (hbound : ∀ x : Point, ∀ r : ℝ, 0 < r → μ (closedBall x r) ≤ ENNReal.ofReal (C*r^d))
    (t c : ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    μ (closedBall (0:Point) 1 ∩ {x | |dot (Boundary.rawNormal t) x-c| ≤ 18*θ}) ≤
      ENNReal.ofReal (13*C*(1+3^d)*36^(d-1)*θ^(d-1)) := by
  let ν := Boundary.rawNormal t
  let a := Real.sqrt (sqNorm ν)
  have ha : 0 < a := Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) (Boundary.rawNormal_bounds t))
  have ha2 : (1:ℝ)/2 ≤ a := by
    have hs := Real.sq_sqrt (show 0 ≤ sqNorm ν from (by norm_num : (0:ℝ) ≤ 1/2).trans (Boundary.rawNormal_bounds t))
    change a^2=sqNorm ν at hs
    have hb := Boundary.rawNormal_bounds t
    change 1/2 ≤ sqNorm ν at hb
    nlinarith
  have hn : sqNorm (a⁻¹ • ν)=1 := normalize_sqNorm ν (by have := Boundary.rawNormal_bounds t; change 1/2 ≤ sqNorm ν at this; linarith)
  have hs : {x : Point | |dot ν x-c| ≤ 18*θ}⊆{x | |dot (a⁻¹ • ν) x-c/a| ≤ 36*θ} := by
    intro x hx
    have he : dot (a⁻¹ • ν) x-c/a=(dot ν x-c)/a := by dsimp [dot]; ring
    change |dot (a⁻¹ • ν) x-c/a| ≤ 36*θ
    rw [he,abs_div,abs_of_pos ha]
    apply (div_le_iff₀ ha).mpr
    change |dot ν x-c| ≤ 18*θ at hx
    have hh := mul_le_mul_of_nonneg_left ha2 (show 0 ≤ 36*θ by positivity)
    nlinarith only [hx,hh]
  apply (measure_mono (inter_subset_inter_right _ hs)).trans
  have hh := strip_bound_of_disk_nonneg μ hC hd hbound (a⁻¹ • ν) hn (c/a) (show 0 ≤ 36*θ by positivity)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 36) hθ] at hh
  simpa only [mul_assoc] using hh

end PlanarHalving.Spatial

namespace PlanarHalving.Limits
open Set Filter MeasureTheory
open scoped Topology
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma eventually_gt_open {μ : FiniteMeasure X} {μs : ℕ → FiniteMeasure X}
    (h : Tendsto μs atTop (𝓝 μ)) {O : Set X} (hO : IsOpen O)
    {q : ℝ} (hq : q < (μ O : ℝ)) : ∀ᶠ n in atTop, q < (μs n O : ℝ) := by
  let ε := ((μ O:ℝ)-q)/3
  have hε : 0<ε := by dsimp [ε]; linarith
  have hadd (ν : FiniteMeasure X) : (ν O:ℝ)+(ν Oᶜ:ℝ)=(ν.mass:ℝ) :=
    measureReal_add_measureReal_compl (μ:=(ν:Measure X)) hO.measurableSet
  have hcomp := eventually_lt_closed h hO.isClosed_compl
    (show (μ Oᶜ:ℝ)<(μ Oᶜ:ℝ)+ε by linarith)
  have hmass := (NNReal.continuous_coe.tendsto _ |>.comp h.mass).eventually
    (eventually_gt_nhds (show (μ.mass:ℝ)-ε<(μ.mass:ℝ) by linarith))
  filter_upwards [hcomp,hmass] with n hn hm
  have hsum := hadd (μs n)
  have hsum' := hadd μ
  dsimp [ε] at hn hm
  linarith

lemma open_le_of_eventually_le {μ : FiniteMeasure X} {μs : ℕ → FiniteMeasure X}
    (h : Tendsto μs atTop (𝓝 μ)) {O : Set X} (hO : IsOpen O)
    {b : ℕ → ℝ} {B : ℝ} (hb : Tendsto b atTop (𝓝 B))
    (hbound : ∀ᶠ n in atTop, (μs n O:ℝ) ≤ b n) : (μ O:ℝ) ≤ B := by
  by_contra hh
  obtain ⟨q,hqB,hqμ⟩ := exists_between (lt_of_not_ge hh)
  obtain ⟨n,hn,hn',hn''⟩ := ((eventually_gt_open h hO hqμ).and
    ((hb.eventually (eventually_lt_nhds hqB)).and hbound)).exists
  exact (not_lt_of_ge hn'') (hn'.trans hn)

end PlanarHalving.Limits

end OAI
