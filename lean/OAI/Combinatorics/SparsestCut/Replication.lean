import OAI.Combinatorics.SparsestCut.CutDuality

namespace OAI

universe u1 u2 u3 u4

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.Replication
variable {V : Type u1} [Fintype V]
def count (M : ℕ) (w : V → ℝ) (v : V) : ℕ := 1+⌊(M:ℝ)*w v⌋₊
def Copies (M : ℕ) (w : V → ℝ) := (v : V) × Fin (count M w v)
instance (M : ℕ) (w : V → ℝ) : Fintype (Copies M w) := inferInstanceAs (Fintype (Sigma _))
def n (M : ℕ) (w : V → ℝ) : ℕ := Fintype.card (Copies M w)
def q (M : ℕ) (w : V → ℝ) (v : V) : ℝ := (count M w v:ℝ)/(n M w:ℝ)
omit [Fintype V] in
lemma count_pos (M : ℕ) (w : V → ℝ) (v : V) : 0<count M w v := by unfold count; omega
lemma n_sum (M : ℕ) (w : V → ℝ) : n M w=∑ v, count M w v := by
  change Fintype.card ((v : V) × Fin (count M w v)) = _
  simp [Fintype.card_sigma]
omit [Fintype V] in
lemma count_error (M : ℕ) (w : V → ℝ) (hw : ∀ v, 0≤w v) (v : V) :
    0<(count M w v:ℝ)-(M:ℝ)*w v ∧ (count M w v:ℝ)-(M:ℝ)*w v≤1 := by
  have h0 : 0≤(M:ℝ)*w v := mul_nonneg (Nat.cast_nonneg _) (hw v)
  have h1 := Nat.floor_le h0
  have h2 := Nat.lt_floor_add_one ((M:ℝ)*w v)
  simp only [count,Nat.cast_add,Nat.cast_one]
  constructor <;> linarith
lemma n_bounds (M : ℕ) (w : V → ℝ) (hw : ∀ v, 0≤w v) (hws : ∑ v, w v=1) :
    M≤n M w ∧ n M w≤M+Fintype.card V := by
  have hs : (n M w:ℝ)-(M:ℝ)=∑ v, ((count M w v:ℝ)-(M:ℝ)*w v) := by
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,hws,mul_one,n_sum,Nat.cast_sum]
  have h0 : 0≤(n M w:ℝ)-(M:ℝ) := by rw [hs]; exact Finset.sum_nonneg (fun v _ => (count_error M w hw v).1.le)
  have h1 : (n M w:ℝ)-(M:ℝ)≤Fintype.card V := by
    rw [hs]
    calc
      _ ≤ ∑ _v : V, (1:ℝ) := Finset.sum_le_sum (fun v _ => (count_error M w hw v).2)
      _ = _ := by simp
  constructor
  · exact_mod_cast (show (M:ℝ)≤n M w by linarith)
  · exact_mod_cast (show (n M w:ℝ)≤(M:ℝ)+Fintype.card V by linarith)
lemma q_nonneg (M : ℕ) (w : V → ℝ) (v : V) : 0≤q M w v := by unfold q; positivity
lemma q_sum (M : ℕ) (w : V → ℝ) (hn : 0<n M w) : ∑ v, q M w v=1 := by
  simp only [q,← Finset.sum_div,← Nat.cast_sum,← n_sum]
  exact div_self (by exact_mod_cast hn.ne')
lemma q_l1_bound (M : ℕ) (hM : 0<M) (w : V → ℝ) (hw : ∀ v, 0≤w v) (hws : ∑ v, w v=1) :
    (∑ v, |q M w v-w v|)≤2*(Fintype.card V:ℝ)/M := by
  have hb := n_bounds M w hw hws
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hn : (0:ℝ)<n M w := lt_of_lt_of_le hMr (by exact_mod_cast hb.1)
  have hE : (n M w:ℝ)-(M:ℝ)=∑ v, ((count M w v:ℝ)-(M:ℝ)*w v) := by
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,hws,mul_one,n_sum,Nat.cast_sum]
  have hE0 : 0≤(n M w:ℝ)-(M:ℝ) := by
    have hh : (M:ℝ)≤n M w := by exact_mod_cast hb.1
    linarith
  have he (v : V) : |q M w v-w v|≤
      (((count M w v:ℝ)-(M:ℝ)*w v)+((n M w:ℝ)-(M:ℝ))*w v)/(n M w:ℝ) := by
    have heq : q M w v-w v=
        (((count M w v:ℝ)-(M:ℝ)*w v)-((n M w:ℝ)-(M:ℝ))*w v)/(n M w:ℝ) := by
      unfold q; field_simp; ring
    rw [heq,abs_div,abs_of_pos hn]
    apply div_le_div_of_nonneg_right _ hn.le
    exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (count_error M w hw v).1.le,abs_of_nonneg (mul_nonneg hE0 (hw v))])
  calc
    _ ≤ ∑ v, (((count M w v:ℝ)-(M:ℝ)*w v)+((n M w:ℝ)-(M:ℝ))*w v)/(n M w:ℝ) := Finset.sum_le_sum (fun v _ => he v)
    _ = 2*((n M w:ℝ)-(M:ℝ))/(n M w:ℝ) := by
      rw [← Finset.sum_div,Finset.sum_add_distrib,← Finset.mul_sum,hws,mul_one,← hE]; ring
    _ ≤ 2*(Fintype.card V:ℝ)/(n M w:ℝ) := by
      apply div_le_div_of_nonneg_right _ hn.le
      have h : (n M w:ℝ)≤(M:ℝ)+Fintype.card V := by exact_mod_cast hb.2
      linarith
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hMr (by exact_mod_cast hb.1)

lemma product_expectation_bound (p q : V → ℝ) (hp : ∀ v, 0≤p v) (hq : ∀ v, 0≤q v)
    (hps : ∑ v, p v=1) (hqs : ∑ v, q v=1) (g : V → V → ℝ) {D : ℝ}
    (_hD : 0≤D) (hg : ∀ v z, |g v z|≤D) :
    |(∑ v, ∑ z, p v*p z*g v z)-(∑ v, ∑ z, q v*q z*g v z)|≤
      2*D*(∑ v, |p v-q v|) := by
  have he (v z : V) : p v*p z*g v z-q v*q z*g v z=
      (p v-q v)*p z*g v z+q v*(p z-q z)*g v z := by ring
  calc
    _ = |∑ v, ∑ z, ((p v-q v)*p z*g v z+q v*(p z-q z)*g v z)| := by
      simp only [← Finset.sum_sub_distrib,he]
    _ ≤ ∑ v, ∑ z, |(p v-q v)*p z*g v z+q v*(p z-q z)*g v z| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun v _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ v, ∑ z, (|p v-q v| *p z*D+q v*|p z-q z| *D) := by
      apply Finset.sum_le_sum; intro v hv
      apply Finset.sum_le_sum; intro z hz
      calc
        _ ≤ |(p v-q v)*p z*g v z|+|q v*(p z-q z)*g v z| := abs_add_le _ _
        _ ≤ _ := by
          rw [abs_mul,abs_mul,abs_mul,abs_mul,abs_of_nonneg (hp z),abs_of_nonneg (hq v)]
          exact add_le_add (mul_le_mul_of_nonneg_left (hg v z) (mul_nonneg (abs_nonneg _) (hp z)))
            (mul_le_mul_of_nonneg_left (hg v z) (mul_nonneg (hq v) (abs_nonneg _)))
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum,hps,hqs,mul_one,one_mul]
      ring
end UniformSparsestCut.Replication

namespace UniformSparsestCut.Replication
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {V : Type u2} [Fintype V]
def rep (M : ℕ) (w : V → ℝ) (i : Fin (n M w)) : V := ((Fintype.equivFin (Copies M w)).symm i).1
def representative (M : ℕ) (w : V → ℝ) (v : V) : Fin (n M w) :=
  (Fintype.equivFin (Copies M w)) ⟨v,⟨0,count_pos M w v⟩⟩
lemma rep_section (M : ℕ) (w : V → ℝ) (v : V) : rep M w (representative M w v)=v := by
  exact congrArg (fun copy : Copies M w => copy.1)
    ((Fintype.equivFin (Copies M w)).symm_apply_apply ⟨v, ⟨0, count_pos M w v⟩⟩)
lemma sum_rep (M : ℕ) (w : V → ℝ) (g : V → ℝ) :
    (∑ i : Fin (n M w), g (rep M w i))=∑ v, (count M w v:ℝ)*g v := by
  classical
  calc
    _ = ∑ c : Copies M w, g (rep M w ((Fintype.equivFin (Copies M w)) c)) :=
      ((Fintype.equivFin (Copies M w)).sum_comp (fun i => g (rep M w i))).symm
    _ = ∑ c : Copies M w, g c.1 := Finset.sum_congr rfl (fun copy _ =>
      congrArg (fun copy : Copies M w => g copy.1)
        ((Fintype.equivFin (Copies M w)).symm_apply_apply copy))
    _ = _ := by
      change (∑ c : (v : V) × Fin (count M w v), g c.1) = _
      simp [Fintype.sum_sigma]
lemma ordered_sum (M : ℕ) (w : V → ℝ) (hn : 0 < n M w) (g : V → V → ℝ) :
    (∑ i : Fin (n M w), ∑ j, g (rep M w i) (rep M w j))=
      (n M w:ℝ)^2*(∑ v, ∑ z, q M w v*q M w z*g v z) := by
  have hn0 : (n M w:ℝ)≠0 := by exact_mod_cast hn.ne'
  calc
    _ = ∑ i : Fin (n M w), ∑ z, (count M w z:ℝ)*g (rep M w i) z :=
      Finset.sum_congr rfl (fun i _ => sum_rep M w (g (rep M w i)))
    _ = ∑ v, (count M w v:ℝ)*(∑ z, (count M w z:ℝ)*g v z) :=
      sum_rep M w (fun v => ∑ z, (count M w z:ℝ)*g v z)
    _ = _ := by
      simp only [Finset.mul_sum,q]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro z hz
      field_simp

lemma collapse (M : ℕ) (w : V → ℝ) (d : V → V → ℝ) (hself : ∀ v, d v v=0)
    {A : Type u3} [Fintype A] (F : Fin (n M w) → A → ℝ)
    (hF : ∀ i j, (∑ a, |F i a-F j a|)≤d (rep M w i) (rep M w j)) (i : Fin (n M w)) (a : A) :
    F i a=F (representative M w (rep M w i)) a := by
  classical
  have h := hF i (representative M w (rep M w i))
  rw [rep_section,hself] at h
  have hh := (Finset.single_le_sum (fun b _ => abs_nonneg (F i b-F (representative M w (rep M w i)) b)) (Finset.mem_univ a)).trans h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hh)
lemma descend_contraction (M : ℕ) (w : V → ℝ) (d : V → V → ℝ)
    {A : Type u4} [Fintype A] (F : Fin (n M w) → A → ℝ)
    (hF : ∀ i j, (∑ a, |F i a-F j a|)≤d (rep M w i) (rep M w j)) :
    ∀ v z, (∑ a, |F (representative M w v) a-F (representative M w z) a|)≤d v z := by
  intro v z
  simpa only [rep_section] using hF (representative M w v) (representative M w z)
lemma expectation_error (M : ℕ) (hM : 0 < M) (w : V → ℝ) (hw : ∀ v, 0≤w v) (hws : (∑ v,w v)=1)
    (g : V → V → ℝ) {D : ℝ} (hD : 0≤D) (hg : ∀ v z, |g v z|≤D) :
    |(∑ v, ∑ z, q M w v*q M w z*g v z)-(∑ v, ∑ z, w v*w z*g v z)|≤
      4*D*(Fintype.card V:ℝ)/M := by
  have hn : 0 < n M w := hM.trans_le (n_bounds M w hw hws).1
  have h := product_expectation_bound (q M w) w (q_nonneg M w) hw (q_sum M w hn) hws g hD hg
  calc
    _ ≤ 2*D*(∑ v, |q M w v-w v|) := h
    _ ≤ 2*D*(2*(Fintype.card V:ℝ)/M) := mul_le_mul_of_nonneg_left (q_l1_bound M hM w hw hws) (by positivity)
    _ = _ := by ring
end
end UniformSparsestCut.Replication

end

end OAI
