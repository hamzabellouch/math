import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Coding.ReconstructionEntropy

namespace OAI

section
namespace HyperbolicCoding.MatrixCoupling
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {p : A → ℝ} {q : B → ℝ}

noncomputable def extendRows (S : Finset A) (g : S → B → ℝ) (a : A) (b : B) : ℝ :=
  if h : a∈S then g ⟨a,h⟩ b else 0

omit [Fintype B] [DecidableEq B] in
lemma sum_extendRows (S : Finset A) (g : S → B → ℝ) (b : B) :
    (∑ a,extendRows S g a b)=∑ a : S,g a b := by
  exact (Finset.sum_attach_eq_sum_dite S (fun a => g a b)).symm

omit [Fintype A] [Fintype B] [DecidableEq B] in
lemma extendRows_nonneg (S : Finset A) (g : S → B → ℝ) (hg : ∀ a b,0≤g a b) (a b) :
    0≤extendRows S g a b := by
  unfold extendRows
  split
  · exact hg _ _
  · rfl

omit [Fintype A] [DecidableEq B] in
lemma extendRows_sum (S : Finset A) (g : S → B → ℝ) (a : A) :
    (∑ b,extendRows S g a b)=if h : a∈S then ∑ b,g ⟨a,h⟩ b else 0 := by
  unfold extendRows
  split <;> simp_all

omit [DecidableEq B] in
lemma sum_extendRows_mul (S : Finset A) (g : S → B → ℝ) (c : A → B → ℝ) :
    (∑ a,∑ b,extendRows S g a b*c a b)=∑ a : S,∑ b,g a b*c a b := by
  have he (a : A) : (∑ b,extendRows S g a b*c a b)=
      if h : a∈S then ∑ b,g ⟨a,h⟩ b*c a b else 0 := by
    unfold extendRows
    split <;> simp_all
  simp_rw [he]
  exact (Finset.sum_attach_eq_sum_dite S (fun a => ∑ b,g a b*c a b)).symm

noncomputable def replaceSub (R : MatrixCoupling p q) (S : Finset A)
    {u : S → ℝ} {v : B → ℝ} (G H : MatrixCoupling u v)
    (hle : ∀ a b,G.weight a b≤R.weight a b) : MatrixCoupling p q where
  weight a b := R.weight a b-extendRows S G.weight a b+extendRows S H.weight a b
  nonneg a b := by
    have hg : extendRows S G.weight a b≤R.weight a b := by
      unfold extendRows
      split
      · exact hle _ _
      · exact R.nonneg _ _
    exact add_nonneg (sub_nonneg.mpr hg) (extendRows_nonneg S _ H.nonneg a b)
  row a := by
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,R.row,extendRows_sum,G.row,H.row]
    ring
  col b := by
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,R.col,sum_extendRows,G.col,H.col]
    ring

omit [DecidableEq B] in
lemma replaceSub_cost (R : MatrixCoupling p q) (S : Finset A)
    {u : S → ℝ} {v : B → ℝ} (G H : MatrixCoupling u v)
    (hle : ∀ a b,G.weight a b≤R.weight a b) (c : A → B → ℝ) :
    (R.replaceSub S G H hle).cost c=R.cost c-G.cost (fun a b => c a b)+H.cost (fun a b => c a b) := by
  unfold cost replaceSub
  simp only [add_mul,sub_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib,sum_extendRows_mul]

omit [DecidableEq B] in
lemma replaceSub_bounded_cost (R : MatrixCoupling p q) (hp : ∑ a,p a=1) (S : Finset A)
    {u : S → ℝ} {v : B → ℝ} (G H : MatrixCoupling u v)
    (hle : ∀ a b,G.weight a b≤R.weight a b) (c : A → B → ℝ) (hc1 : ∀ a b,c a b≤1) :
    (R.replaceSub S G H hle).cost c≤1-(∑ a,u a)+H.cost (fun a b => c a b) := by
  have hres (a : A) (b : B) : 0≤R.weight a b-extendRows S G.weight a b := by
    apply sub_nonneg.mpr
    unfold extendRows
    split
    · exact hle _ _
    · exact R.nonneg _ _
  have hb : (∑ a,∑ b,(R.weight a b-extendRows S G.weight a b)*c a b)≤1-(∑ a,u a) := by
    calc
      _≤∑ a,∑ b,(R.weight a b-extendRows S G.weight a b) := by
        apply Finset.sum_le_sum; intro a _
        apply Finset.sum_le_sum; intro b _
        exact mul_le_of_le_one_right (hres a b) (hc1 a b)
      _=_ := by
        simp only [Finset.sum_sub_distrib,R.row,hp]
        congr 1
        rw [Finset.sum_comm]
        simp only [sum_extendRows]
        rw [Finset.sum_comm]
        simp only [G.row]
  rw [replaceSub_cost]
  have he : R.cost c-G.cost (fun a b => c a b)=
      ∑ a,∑ b,(R.weight a b-extendRows S G.weight a b)*c a b := by
    simp only [sub_mul,Finset.sum_sub_distrib,sum_extendRows_mul,cost]
  rw [he]
  linarith

noncomputable def divide (R : MatrixCoupling p q) {t : ℝ} (ht : 0<t) :
    MatrixCoupling (fun a => p a/t) (fun b => q b/t) where
  weight a b := R.weight a b/t
  nonneg a b := div_nonneg (R.nonneg a b) ht.le
  row a := by rw [←Finset.sum_div,R.row]
  col b := by rw [←Finset.sum_div,R.col]

omit [DecidableEq A] [DecidableEq B] in
lemma divide_cost (R : MatrixCoupling p q) {t : ℝ} (ht : 0<t) (c : A → B → ℝ) :
    (R.divide ht).cost c=R.cost c/t := by
  simp only [cost,divide,div_mul_eq_mul_div,←Finset.sum_div]

theorem decodable_coupling_total [Nonempty A] {ε : ℝ} (hε : 0<ε)
    (R : MatrixCoupling p q) (t : ℝ) (ht : 0<t) (hsum : (∑ b,q b)=t)
    (c : A → B → ℝ) (hc0 : ∀ a b,0≤c a b) (hc1 : ∀ a b,c a b≤1)
    (M : ℝ) (hM : ∀ b,q b≤M) (hsmall : (Fintype.card A : ℝ)*M≤t*decodingThreshold ε) :
    ∃ (D : B → A) (H : MatrixCoupling p q),
      H.cost (fun a b => symbolCost a (D b))<t*ε ∧ H.cost c<R.cost c+t*ε := by
  let V := R.divide ht
  have hVs : (∑ b,q b/t)=1 := by rw [←Finset.sum_div,hsum,div_self ht.ne']
  have hVm : ∀ b,q b/t≤M/t := fun b => div_le_div_of_nonneg_right (hM b) ht.le
  have hsize : (Fintype.card A : ℝ)*(M/t)≤decodingThreshold ε := by
    rw [←mul_div_assoc]
    exact (div_le_iff₀ ht).mpr (by simpa only [mul_comm] using hsmall)
  obtain ⟨D,H,hD,hH⟩ := decodable_coupling_tolerance hε V hVs c hc0 hc1 (M/t) hVm hsize
  let W : MatrixCoupling p q := {
    weight a b := t*H.weight a b
    nonneg a b := mul_nonneg ht.le (H.nonneg a b)
    row a := by rw [←Finset.mul_sum,H.row]; exact mul_div_cancel₀ _ ht.ne'
    col b := by rw [←Finset.mul_sum,H.col]; exact mul_div_cancel₀ _ ht.ne' }
  have hwcost (d : A → B → ℝ) : W.cost d=t*H.cost d := by
    unfold cost
    simp only [W,mul_assoc,←Finset.mul_sum]
  refine ⟨D,W,?_,?_⟩
  · rw [hwcost]
    exact mul_lt_mul_of_pos_left hD ht
  · rw [hwcost]
    have h := mul_lt_mul_of_pos_left hH ht
    rw [show V.cost c=R.cost c/t from R.divide_cost ht c] at h
    rw [mul_add,mul_div_cancel₀ _ ht.ne'] at h
    exact h

theorem decodable_subtransport {ε : ℝ} (hε : 0<ε)
    (R : MatrixCoupling p q) (hp : ∑ a,p a=1) (S : Finset A) (hS : S.Nonempty)
    {u : S → ℝ} {v : B → ℝ} (G : MatrixCoupling u v)
    (hle : ∀ a b,G.weight a b≤R.weight a b) (t : ℝ) (ht : 0<t) (hsum : (∑ a,u a)=t)
    (c : A → B → ℝ) (hc0 : ∀ a b,0≤c a b) (hc1 : ∀ a b,c a b≤1)
    (M : ℝ) (hM : ∀ b,v b≤M) (hsmall : (S.card : ℝ)*M≤t*decodingThreshold ε) :
    ∃ (D : B → A) (H : MatrixCoupling p q),
      H.cost (fun a b => symbolCost a (D b))<1-t+t*ε ∧ H.cost c<R.cost c+t*ε := by
  obtain ⟨a,ha⟩ := hS
  have : Nonempty S := ⟨⟨a,ha⟩⟩
  have hsumv : (∑ b,v b)=t := by
    simp_rw [←G.col]
    rw [Finset.sum_comm]
    simp only [G.row,hsum]
  obtain ⟨D,H,hD,hH⟩ := decodable_coupling_total hε G t ht hsumv
    (fun a b => c a b) (fun a b => hc0 a b) (fun a b => hc1 a b) M hM (by simpa using hsmall)
  let D' : B → A := fun b => (D b).val
  let H' := R.replaceSub S G H hle
  have he (a : S) (b : B) : symbolCost (a : A) (D' b)=symbolCost a (D b) := by
    simp only [symbolCost,D',Subtype.val_inj]
    split_ifs <;> rfl
  have hb := R.replaceSub_bounded_cost hp S G H hle (fun a b => symbolCost a (D' b))
    (fun a b => symbolCost_le_one a (D' b))
  simp_rw [he] at hb
  rw [hsum] at hb
  refine ⟨D',H',by dsimp only [H']; linarith,?_⟩
  dsimp only [H']
  rw [replaceSub_cost]
  linarith

noncomputable def rectangle (R : MatrixCoupling p q) (S : Finset A) (T : Finset B) :
    MatrixCoupling (fun a : S => ∑ b,if b∈T then R.weight a b else 0)
      (fun b => ∑ a : S,if b∈T then R.weight a b else 0) where
  weight a b := if b∈T then R.weight a b else 0
  nonneg a b := by split <;> first | exact R.nonneg _ _ | exact le_rfl
  row _ := rfl
  col _ := rfl

omit [DecidableEq A] in
lemma rectangle_weight_le (R : MatrixCoupling p q) (S : Finset A) (T : Finset B) (a : S) (b : B) :
    (R.rectangle S T).weight a b≤R.weight a b := by
  dsimp [rectangle]
  split
  · exact le_rfl
  · exact R.nonneg _ _

omit [DecidableEq B] in
lemma sum_subtype_weight_le (R : MatrixCoupling p q) (S : Finset A) (b : B) :
    (∑ a : S,R.weight a b)≤q b := by
  rw [←sum_extendRows S (fun a b => R.weight a b) b,←R.col b]
  apply Finset.sum_le_sum
  intro a _
  unfold extendRows
  split
  · exact le_rfl
  · exact R.nonneg _ _

lemma rectangle_right_bound (R : MatrixCoupling p q) (S : Finset A) (T : Finset B)
    {M : ℝ} (hM0 : 0≤M) (hM : ∀ b∈T,q b≤M) (b : B) :
    (∑ a : S,if b∈T then R.weight a b else 0)≤M := by
  by_cases hb : b∈T
  · simpa only [ite_eq_left hb] using (R.sum_subtype_weight_le S b).trans (hM b hb)
  · simpa only [ite_eq_right hb,Finset.sum_const_zero] using hM0

omit [DecidableEq A] in
lemma rectangle_mass (R : MatrixCoupling p q) (S : Finset A) (T : Finset B) :
    (∑ a : S,∑ b,if b∈T then R.weight a b else 0)=∑ a∈S,∑ b∈T,R.weight a b := by
  simp only [Finset.sum_ite_mem,Finset.univ_inter]
  exact (Finset.sum_subtype S (fun _ => Iff.rfl) (fun a : A => ∑ b∈T,R.weight a b)).symm

omit [DecidableEq A] in
lemma rectangle_mass_ge (R : MatrixCoupling p q) (hp : ∑ a,p a=1) (S : Finset A) (T : Finset B) :
    (∑ a∈S,p a)+(∑ b∈T,q b)-1≤∑ a : S,∑ b,if b∈T then R.weight a b else 0 := by
  rw [rectangle_mass]
  have hsplit : (∑ a∈S,p a)=(∑ a∈S,∑ b∈T,R.weight a b)+(∑ a∈S,∑ b∈Tᶜ,R.weight a b) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_add_sum_compl,R.row]
  have hbad : (∑ a∈S,∑ b∈Tᶜ,R.weight a b)≤∑ b∈Tᶜ,q b := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro b _
    rw [←R.col b]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun a _ _ => R.nonneg a b)
  have htotal : (∑ b∈T,q b)+(∑ b∈Tᶜ,q b)=1 := by
    rw [Finset.sum_add_sum_compl]
    simp_rw [←R.col]
    rw [Finset.sum_comm]
    simp only [R.row,hp]
  linarith

theorem decodable_typical_coupling {ε θ : ℝ} (hε : 0 < ε)
    (_hθ : 0 ≤ θ) (hθsmall : θ < 1/2)
    (R : MatrixCoupling p q) (hp : ∑ a,p a=1)
    (S : Finset A) (T : Finset B)
    (hS : 1-θ ≤ ∑ a∈S,p a) (hT : 1-θ ≤ ∑ b∈T,q b)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ b∈T,q b ≤ M)
    (hsize : (S.card : ℝ)*M ≤ (1-2*θ)*decodingThreshold ε)
    (c : A → B → ℝ) (hc0 : ∀ a b,0 ≤ c a b) (hc1 : ∀ a b,c a b ≤ 1) :
    ∃ (D : B → A) (H : MatrixCoupling p q),
      H.cost (fun a b => symbolCost a (D b)) < 2*θ+ε ∧ H.cost c < R.cost c+ε := by
  let G := R.rectangle S T
  let t : ℝ := ∑ a : S,∑ b,if b∈T then R.weight a b else 0
  have htlo : 1-2*θ ≤ t := by
    have h := R.rectangle_mass_ge hp S T
    dsimp only [t]
    linarith
  have ht : 0 < t := by linarith
  have hthi : t ≤ 1 := by
    dsimp only [t]
    rw [R.rectangle_mass]
    calc
      _ ≤ ∑ a∈S,∑ b,R.weight a b := by
        apply Finset.sum_le_sum
        intro a _
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
          (fun b _ _ => R.nonneg a b)
      _ = ∑ a∈S,p a := by simp only [R.row]
      _ ≤ ∑ a,p a := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          (fun a _ _ => R.left_nonneg a)
      _ = 1 := hp
  have hSne : S.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he,Finset.sum_empty] at hS
    linarith
  have hthreshold : 0 ≤ decodingThreshold ε := (decodingThreshold_pos hε).le
  have hsize' : (S.card : ℝ)*M ≤ t*decodingThreshold ε :=
    hsize.trans (mul_le_mul_of_nonneg_right htlo hthreshold)
  obtain ⟨D,H,hD,hH⟩ := decodable_subtransport hε R hp S hSne G
    (R.rectangle_weight_le S T) t ht rfl c hc0 hc1 M
    (R.rectangle_right_bound S T hM0 hM) hsize'
  have hte : t*ε ≤ ε := mul_le_of_le_one_left hε.le hthi
  exact ⟨D,H,by linarith,by linarith⟩

end HyperbolicCoding.MatrixCoupling

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

noncomputable def pushWeight (q : A → ℝ) (f : A → B) (b : B) : ℝ :=
  ∑ a,if f a=b then q a else 0

lemma pushWeight_sum (q : A → ℝ) (f : A → B) :
    (∑ b,pushWeight q f b)=∑ a,q a := by
  unfold pushWeight
  rw [Finset.sum_comm]
  simp

omit [Fintype B] in
lemma pushWeight_nonneg (q : A → ℝ) (hq : ∀ a,0 ≤ q a) (f : A → B) (b : B) :
    0 ≤ pushWeight q f b := by
  apply Finset.sum_nonneg
  intro a _
  split <;> first | exact hq a | exact le_rfl

omit [Fintype B] in
lemma pushWeight_add (q r : A → ℝ) (f : A → B) (b : B) :
    pushWeight (fun a => q a+r a) f b=pushWeight q f b+pushWeight r f b := by
  simp only [pushWeight,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split <;> simp

omit [Fintype B] in
lemma pushWeight_bound (q : A → ℝ) (f : A → B) {M K : ℝ} (hM : ∀ a,q a ≤ M)
    (hM0 : 0 ≤ M) (hf : ∀ b,(Fintype.card {a // f a=b} : ℝ) ≤ K) (b : B) :
    pushWeight q f b ≤ K*M := by
  calc
    _ ≤ ∑ a : A,if f a=b then M else 0 := by
      apply Finset.sum_le_sum
      intro a _
      split <;> first | exact hM a | exact le_rfl
    _ = (Fintype.card {a // f a=b} : ℝ)*M := by
      simp only [Finset.sum_ite,Finset.sum_const,nsmul_eq_mul,mul_zero,add_zero]
      congr 1
      rw [Fintype.card_subtype]
    _ ≤ K*M := mul_le_mul_of_nonneg_right (hf b) hM0

theorem typical_pushforward [DecidableEq A]
    (q : A → ℝ) (hq : ∀ a,0 ≤ q a) (hs : ∑ a,q a=1)
    (f : A → B) (S : Finset A) {M K ε : ℝ} (hM0 : 0 ≤ M) (_hK0 : 0 ≤ K)
    (hM : ∀ a∈S,q a ≤ M) (hf : ∀ b,(Fintype.card {a // f a=b} : ℝ) ≤ K)
    (hbad : (∑ a : A,if a∉S then q a else 0) ≤ ε) :
    ∃ T : Finset B,
      (∀ b∈T,pushWeight q f b ≤ 2*K*M) ∧
      1-2*ε ≤ ∑ b∈T,pushWeight q f b := by
  let u : A → ℝ := fun a => if a∈S then q a else 0
  let v : A → ℝ := fun a => if a∉S then q a else 0
  have hu0 : ∀ a,0 ≤ u a := by intro a; dsimp [u]; split <;> first | exact hq a | exact le_rfl
  have hv0 : ∀ a,0 ≤ v a := by intro a; dsimp [v]; split <;> first | exact hq a | exact le_rfl
  have huM : ∀ a,u a ≤ M := by
    intro a; dsimp [u]; split
    · exact hM a ‹_›
    · exact hM0
  have heq (a : A) : q a=u a+v a := by
    dsimp [u,v]
    by_cases ha : a∈S <;> simp [ha]
  have hpush (b : B) : pushWeight q f b=pushWeight u f b+pushWeight v f b := by
    conv_lhs => rw [show q=(fun a => u a+v a) from funext heq]
    exact pushWeight_add u v f b
  have hub (b : B) : pushWeight u f b ≤ K*M := pushWeight_bound u f huM hM0 hf b
  let T := Finset.univ.filter (fun b => pushWeight v f b ≤ K*M)
  have hmem (b : B) : b∈T ↔ pushWeight v f b ≤ K*M := by simp [T]
  refine ⟨T,?_,?_⟩
  · intro b hb
    rw [hmem] at hb
    rw [hpush]
    linarith [hub b]
  · have hout : (∑ b∈Tᶜ,pushWeight q f b) ≤ 2*ε := by
      calc
        _ ≤ ∑ b∈Tᶜ,2*pushWeight v f b := by
          apply Finset.sum_le_sum
          intro b hb
          have hnot : K*M < pushWeight v f b := by
            have := Finset.mem_compl.mp hb
            rw [hmem] at this
            exact lt_of_not_ge this
          rw [hpush]
          linarith [hub b]
        _ = 2*(∑ b∈Tᶜ,pushWeight v f b) := by rw [Finset.mul_sum]
        _ ≤ 2*(∑ b,pushWeight v f b) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun b _ _ => pushWeight_nonneg v hv0 f b)
        _ ≤ 2*ε := by rw [pushWeight_sum]; exact mul_le_mul_of_nonneg_left hbad (by norm_num)
    have hsplit : (∑ b∈T,pushWeight q f b)+(∑ b∈Tᶜ,pushWeight q f b)=1 := by
      rw [Finset.sum_add_sum_compl,pushWeight_sum,hs]
    linarith

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ}
noncomputable def pushRight [DecidableEq C] (R : MatrixCoupling p q) (f : B → C) :
    MatrixCoupling p (pushWeight q f) where
  weight a c := pushWeight (R.weight a) f c
  nonneg a c := pushWeight_nonneg _ (R.nonneg a) _ c
  row a := by rw [pushWeight_sum,R.row]
  col c := by
    simp only [pushWeight]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    split
    · exact R.col b
    · simp

lemma pushRight_cost [DecidableEq C] (R : MatrixCoupling p q) (f : B → C) (c : A → C → ℝ) :
    (R.pushRight f).cost c=R.cost (fun a b => c a (f b)) := by
  simp only [cost,pushRight,pushWeight,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

end MatrixCoupling

omit [Fintype A] in
lemma mass_mem_finset {X : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → A) (hp : Measurable p) (S : Finset A) :
    (∑ a∈S,mass μ p a)=μ.real {x | p x∈S} := by
  have hm (a : A) : mass μ p a=(μ.map p).real {a} :=
    (map_measureReal_apply hp (measurableSet_singleton a)).symm
  simp_rw [hm]
  rw [sum_measureReal_singleton,map_measureReal_apply hp S.measurableSet]
  rfl

omit [Fintype A] in
lemma mass_codebook_lower {X : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (hp : Measurable p) (S : Finset A) {ε : ℝ}
    (hbad : μ.real {x | p x∉S}<ε) : 1-ε < ∑ a∈S,mass μ p a := by
  rw [mass_mem_finset μ p hp S]
  have hh := measureReal_add_measureReal_compl (μ:=μ) (hp S.measurableSet)
  have he : (p ⁻¹' (S : Set A))ᶜ={x | p x∉S} := rfl
  rw [he] at hh
  simp only [Measure.real,measure_univ,ENNReal.toReal_one] at hh
  change μ.real {x | p x∈S}+μ.real {x | p x∉S}=1 at hh
  linarith

end HyperbolicCoding

end
section
namespace HyperbolicCoding.MatrixCoupling
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {p : A → ℝ} {q : B → ℝ}

theorem decodable_after_sanitizing {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 ≤ θ)
    (hθsmall : θ < 1/4) (R : MatrixCoupling p q) (hp : ∑ a,p a=1)
    (S : Finset A) (T : Finset B) (hS : 1-θ ≤ ∑ a∈S,p a)
    (hbad : (∑ b : B,if b∉T then q b else 0) ≤ θ)
    (f : B → B) (M K : ℝ) (hM0 : 0 ≤ M) (hK0 : 0 ≤ K)
    (hM : ∀ b∈T,q b ≤ M) (hf : ∀ b,(Fintype.card {v // f v=b} : ℝ) ≤ K)
    (hsize : (S.card : ℝ)*(2*K*M) ≤ (1-4*θ)*decodingThreshold ε)
    (c : A → B → ℝ) (hc0 : ∀ a b,0 ≤ c a b) (hc1 : ∀ a b,c a b ≤ 1)
    (κ : ℝ) (hcmap : ∀ a b,c a (f b) ≤ c a b+κ) :
    ∃ (D : B → A) (H : MatrixCoupling p (pushWeight q f)),
      H.cost (fun a b => symbolCost a (D b)) < 4*θ+ε ∧
      H.cost c < R.cost c+κ+ε := by
  have hq : (∑ b,q b)=1 := by
    simp_rw [←R.col]
    rw [Finset.sum_comm]
    simp only [R.row,hp]
  obtain ⟨V,hVm,hV⟩ := typical_pushforward q R.right_nonneg hq f T hM0 hK0 hM hf hbad
  have hs2 : 1-2*θ ≤ ∑ a∈S,p a := by linarith
  have hsize' : (S.card : ℝ)*(2*K*M) ≤ (1-2*(2*θ))*decodingThreshold ε := by
    convert hsize using 1
    ring
  obtain ⟨D,H,hD,hH⟩ := decodable_typical_coupling hε (show 0 ≤ 2*θ by positivity)
    (show 2*θ < 1/2 by linarith) (R.pushRight f) hp S V hs2 hV (2*K*M)
    (by positivity) hVm hsize' c hc0 hc1
  have hcost : (R.pushRight f).cost c ≤ R.cost c+κ := by
    rw [pushRight_cost]
    have h := R.cost_mono (fun a b => c a (f b)) (fun a b => 1*c a b+κ)
      (fun a b => by simpa only [one_mul] using hcmap a b)
    rw [R.cost_affine hp 1 κ c,one_mul] at h
    exact h
  refine ⟨D,H,?_,?_⟩ <;> linarith

theorem marked_word_decodable_coupling {C : Type*} [Fintype C] [DecidableEq C]
    {n r : ℕ} {u : C → ℝ} (β : A → ℝ) (_hβ : ∀ a,0 ≤ β a) (_hβsum : ∑ a,β a=1)
    {ε θ L : ℝ} (hε : 0 < ε) (hθ : 0 ≤ θ) (hθsmall : θ < 1/4)
    (R : MatrixCoupling u (productWordWeight β n)) (hu : ∑ a,u a=1)
    (S : Finset C) (T : Finset (Fin n → A)) (hS : 1-θ ≤ ∑ a∈S,u a)
    (hT : ∀ w∈T,productWordWeight β n w ≤ Real.exp (-L))
    (hbad : (∑ w : Fin n → A,if w∉T then productWordWeight β n w else 0) ≤ θ)
    (zero one : A)
    (hsize : (S.card : ℝ)*(2*(Fintype.card A : ℝ)^(Marker.reserved n r).card*Real.exp (-L)) ≤
      (1-4*θ)*decodingThreshold ε)
    (c : C → (Fin n → A) → ℝ) (hc0 : ∀ a b,0 ≤ c a b) (hc1 : ∀ a b,c a b ≤ 1)
    (κ : ℝ) (hcmap : ∀ a b,c a (Marker.markWord r zero one b) ≤ c a b+κ) :
    ∃ (D : (Fin n → A) → C)
      (H : MatrixCoupling u (pushWeight (productWordWeight β n) (Marker.markWord r zero one))),
      H.cost (fun a b => symbolCost a (D b)) < 4*θ+ε ∧
      H.cost c < R.cost c+κ+ε := by
  apply decodable_after_sanitizing hε hθ hθsmall R hu S T hS hbad
    (Marker.markWord r zero one) (Real.exp (-L)) ((Fintype.card A : ℝ)^(Marker.reserved n r).card)
    (Real.exp_pos _).le (by positivity) hT _ hsize c hc0 hc1 κ hcmap
  intro b
  exact_mod_cast Marker.markWord_fiber_card (r:=r) zero one b

end HyperbolicCoding.MatrixCoupling

end

end OAI
