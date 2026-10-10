import Mathlib
import OAI.Analysis.HardSphere.Geometry.BinaryValue

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped ENNReal NNReal
namespace HardSphere.Lattice

lemma block_scale (k : ℕ) (hk : 2 ≤ k) :
    ∃ q : ℕ, 2 * 3^q ≤ k ∧ k < 6 * 3^q := by
  refine ⟨Nat.log 3 (k/2), ?_, ?_⟩
  · have h := Nat.pow_log_le_self 3 (x := k/2) (by omega)
    omega
  · have h := Nat.lt_pow_succ_log_self (by omega : 1 < 3) (k/2)
    rw [pow_succ] at h
    omega

lemma aligned_block_exists (m q u k : ℕ) (hk : 2 * 3^q ≤ k) (ht : u+k ≤ 3^m) :
    q ≤ m ∧ ∃ b : ℕ, b < 3^(m-q) ∧ u ≤ b * 3^q ∧ (b+1)*3^q ≤ u+k := by
  have hq : q ≤ m := (Nat.pow_le_pow_iff_right (by omega : 1 < 3)).mp (by omega)
  have hn : 0 < 3^q := pow_pos (by omega) _
  have hd := Nat.div_add_mod u (3^q)
  have hm := Nat.mod_lt u hn
  have hbottom : u ≤ (u / 3^q+1)*3^q := by nlinarith
  have htop : (u / 3^q+1+1)*3^q ≤ u+k := by
    calc
      _ = u / 3^q * 3^q + 2 * 3^q := by ring
      _ ≤ u+k := Nat.add_le_add (Nat.div_mul_le_self u (3^q)) hk
  refine ⟨hq, u / 3^q+1, ?_, hbottom, htop⟩
  have hp : 3^m = 3^(m-q)*3^q := by rw [← pow_add, Nat.sub_add_cancel hq]
  rw [hp] at ht
  nlinarith

def sigma : ℝ := Real.log 2 / Real.log 3

lemma sigma_gt_half : 1/2 < sigma := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog := Real.log_lt_log (by norm_num : (0:ℝ)<3) (by norm_num : (3:ℝ)<2*2)
  rw [Real.log_mul (by norm_num) (by norm_num)] at hlog
  rw [sigma, lt_div_iff₀ h3]
  linarith

lemma sigma_pos : 0 < sigma := lt_trans (by norm_num) sigma_gt_half

lemma three_rpow_sigma : (3:ℝ)^sigma = 2 := by
  rw [Real.rpow_def_of_pos (by norm_num), sigma, mul_div_cancel₀ _ (Real.log_ne_zero.mpr
    ⟨by norm_num, by norm_num, by norm_num⟩), Real.exp_log (by norm_num)]

lemma atom_power_bound (k q : ℕ) (hk : 0 < k) (hq : k < 6 * 3^q) :
    ((2:ℝ≥0∞)^q)⁻¹ ≤ ENNReal.ofReal ((6:ℝ)^sigma * (k:ℝ)^(-sigma)) := by
  have hkn : (0:ℝ) < k := by exact_mod_cast hk
  have hq' : (k:ℝ) ≤ 6 * (3:ℝ)^q := by exact_mod_cast hq.le
  have hpow := Real.rpow_le_rpow hkn.le hq' sigma_pos.le
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_pow_comm (by norm_num),
    three_rpow_sigma] at hpow
  have hreal : ((2:ℝ)^q)⁻¹ ≤ (6:ℝ)^sigma * (k:ℝ)^(-sigma) := by
    rw [Real.rpow_neg hkn.le, ← div_eq_mul_inv]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hkn _)).mpr
    rw [mul_comm, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    simpa [mul_comm] using hpow
  have := ENNReal.ofReal_le_ofReal hreal
  simpa [ENNReal.ofReal_inv_of_pos (by positivity : 0 < (2:ℝ)^q),
    ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)] using this

theorem prediction (m u k : ℕ) (hk : 0 < k) (ht : u+k ≤ 3^m) (H : List ℤ) (x : ℤ) :
    ((PMF.uniformOfFintype (TreeNoise m)).map
      (fun w ↦ (incrementHistory m u w, walk m w (u+k)))) (H,x) ≤
    ENNReal.ofReal ((6:ℝ)^sigma * (k:ℝ)^(-sigma)) *
      ((PMF.uniformOfFintype (TreeNoise m)).map (incrementHistory m u)) H := by
  classical
  by_cases hk2 : 2 ≤ k
  · obtain ⟨q, hq, hq'⟩ := block_scale k hk2
    obtain ⟨hqm, b, hb, hu, hv⟩ := aligned_block_exists m q u k hq ht
    have hm : q+(m-q) = m := Nat.add_sub_of_le hqm
    have hh := aligned_prediction q (m-q) b u (u+k) hb hu hv H x
    rw [hm] at hh
    exact hh.trans (mul_le_mul_left (atom_power_bound k q hk hq') _)
  · have hk1 : k = 1 := by omega
    subst k
    have ha : (1:ℝ≥0∞) ≤ ENNReal.ofReal ((6:ℝ)^sigma * (1:ℝ)^(-sigma)) := by
      have hh : (1:ℝ) ≤ (6:ℝ)^sigma := Real.one_le_rpow (by norm_num) sigma_pos.le
      simpa using ENNReal.ofReal_le_ofReal hh
    have hh : ((PMF.uniformOfFintype (TreeNoise m)).map
        (fun w ↦ (incrementHistory m u w, walk m w (u+1)))) (H,x) ≤
        ((PMF.uniformOfFintype (TreeNoise m)).map (incrementHistory m u)) H := by
      simp only [PMF.map_apply, Prod.mk.injEq]
      apply ENNReal.tsum_le_tsum
      intro w
      split_ifs <;> simp_all
    exact hh.trans (by simpa using (mul_le_mul_left ha
      (((PMF.uniformOfFintype (TreeNoise m)).map (incrementHistory m u)) H)))

@[simp] theorem walk_zero (m : ℕ) (w : TreeNoise m) : walk m w 0 = 0 := by simp [walk]

theorem walk_increment (m : ℕ) (w : TreeNoise m) (j : ℕ) (hj : j < 3^m) :
    |walk m w (j+1) - walk m w j| = 1 := by
  have hl : j < (leaves m 1 w).length := by simpa using hj
  rw [walk, walk, List.take_succ_eq_append_getElem hl, List.sum_append]
  simp only [List.sum_cons, List.sum_nil, add_zero, add_sub_cancel_left]
  exact abs_of_mem_leaves (by norm_num) w (List.getElem_mem hl)

lemma map_pair_fiber {A B C : Type*} [DecidableEq B] [DecidableEq C]
    (p : PMF (A × C)) (g : A → B) (H : B) (x : C) :
    (p.map (fun z ↦ (g z.1,z.2))) (H,x) =
      ∑' a, if H = g a then p (a,x) else 0 := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_prod']
  congr 1
  funext a
  by_cases h : H = g a
  · simp [Prod.mk.injEq, h]
  · simp [Prod.mk.injEq, h]

lemma conditional_push_history {A B C : Type*} (p : PMF (A × C)) (g : A → B)
    (a : ℝ≥0∞) (ha : ∀ h x, p (h,x) ≤ a * (p.map Prod.fst) h) (H : B) (x : C) :
    (p.map (fun z ↦ (g z.1,z.2))) (H,x) ≤ a * (p.map (g ∘ Prod.fst)) H := by
  classical
  rw [map_pair_fiber, ← PMF.map_comp, PMF.map_apply, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro h
  split_ifs with hh
  · exact ha h x
  · simp

def positionHistory (m u : ℕ) (w : TreeNoise m) : Fin (u+1) → ℤ := fun j ↦ walk m w j.val

def positionsFromIncrements (u : ℕ) (l : List ℤ) : Fin (u+1) → ℤ :=
  fun j ↦ (l.take j.val).sum

lemma positionHistory_eq (m u : ℕ) (w : TreeNoise m) :
    positionHistory m u w = positionsFromIncrements u (incrementHistory m u w) := by
  funext j
  have hj : j.val ≤ u := by omega
  simp [positionHistory, positionsFromIncrements, incrementHistory, walk, List.take_take,
    min_eq_left hj]

theorem position_prediction (m u k : ℕ) (hk : 0 < k) (ht : u+k ≤ 3^m)
    (H : Fin (u+1) → ℤ) (x : ℤ) :
    ((PMF.uniformOfFintype (TreeNoise m)).map
      (fun w ↦ (positionHistory m u w, walk m w (u+k)))) (H,x) ≤
    ENNReal.ofReal ((6:ℝ)^sigma * (k:ℝ)^(-sigma)) *
      ((PMF.uniformOfFintype (TreeNoise m)).map (positionHistory m u)) H := by
  let p := (PMF.uniformOfFintype (TreeNoise m)).map
      (fun w ↦ (incrementHistory m u w, walk m w (u+k)))
  have hp : ∀ h x, p (h,x) ≤ ENNReal.ofReal ((6:ℝ)^sigma * (k:ℝ)^(-sigma)) *
      (p.map Prod.fst) h := by
    intro h x
    simpa [p, PMF.map_comp, Function.comp_def] using prediction m u k hk ht h x
  have hh := conditional_push_history p (positionsFromIncrements u) _ hp H x
  simpa only [p, PMF.map_comp, Function.comp_def, ← positionHistory_eq] using hh

theorem finite_prediction_walk (T : ℕ) : ∃ m : ℕ, T ≤ 3^m ∧
    (∀ w : TreeNoise m, walk m w 0 = 0) ∧
    (∀ (w : TreeNoise m) j, j < T → |walk m w (j+1) - walk m w j| = 1) ∧
    ∀ u k, 0 < k → u+k ≤ T → ∀ (H : Fin (u+1) → ℤ) (x : ℤ),
      ((PMF.uniformOfFintype (TreeNoise m)).map
        (fun w ↦ (positionHistory m u w, walk m w (u+k)))) (H,x) ≤
      ENNReal.ofReal ((6:ℝ)^sigma * (k:ℝ)^(-sigma)) *
        ((PMF.uniformOfFintype (TreeNoise m)).map (positionHistory m u)) H := by
  have ht : T ≤ 3^T := (Nat.lt_pow_self (by omega : 1 < 3)).le
  exact ⟨T, ht, walk_zero T, fun w j hj ↦ walk_increment T w j (hj.trans_le ht),
    fun u k hk hu H x ↦ position_prediction T u k hk (hu.trans ht) H x⟩

def independentPair {A B : Type*} (p : PMF A) (q : PMF B) : PMF (A × B) :=
  p.bind fun a ↦ q.map fun b ↦ (a,b)

lemma independentPair_apply {A B : Type*} (p : PMF A) (q : PMF B) (a : A) (b : B) :
    independentPair p q (a,b) = p a * q b := by
  classical
  simp only [independentPair, PMF.bind_apply, PMF.map_apply, Prod.mk.injEq]
  calc
    _ = ∑' a', if a = a' then p a' * q b else 0 := by
      apply tsum_congr
      intro a'
      by_cases h : a = a'
      · simp [h]
      · simp [h]
    _ = _ := by simp

lemma independentPair_map {A B C D : Type*} (p : PMF A) (q : PMF B)
    (f : A → C) (g : B → D) :
    (independentPair p q).map (fun z ↦ (f z.1,g z.2)) =
      independentPair (p.map f) (q.map g) := by
  simp only [independentPair, PMF.map_bind, PMF.map_comp, PMF.bind_map,
    Function.comp_def]

lemma pmf_fst {A B : Type*} (p : PMF (A × B)) (a : A) :
    (p.map Prod.fst) a = ∑' b, p (a,b) := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_prod', ENNReal.tsum_comm]
  simp

lemma enn_tsum_ite_const {A : Type*} (P : Prop) [Decidable P] (f : A → ℝ≥0∞) :
    (∑' a, if P then f a else 0) = if P then ∑' a, f a else 0 := by
  by_cases h : P <;> simp [h]

lemma independent_difference_fiber {H J : Type*} (p : PMF (H × ℤ)) (q : PMF (J × ℤ))
    (h : H) (j : J) (z : ℤ) :
    ((independentPair p q).map (fun v ↦ ((v.1.1,v.2.1),v.1.2-v.2.2))) ((h,j),z) =
      ∑' y : ℤ, p (h,z+y) * q (j,y) := by
  classical
  rw [PMF.map_apply]
  simp only [ENNReal.tsum_prod', independentPair_apply, Prod.mk.injEq]
  simp_rw [show ∀ x y : ℤ, z = x-y ↔ x = z+y by omega]
  simp only [ite_and]
  simp_rw [enn_tsum_ite_const]
  simp only [tsum_ite_eq']
  rw [ENNReal.tsum_comm]
  simp

lemma independent_difference_bound {H J : Type*} (p : PMF (H × ℤ)) (q : PMF (J × ℤ))
    (b : ℝ≥0∞) (hp : ∀ h x, p (h,x) ≤ b * (p.map Prod.fst) h)
    (h : H) (j : J) (z : ℤ) :
    ((independentPair p q).map (fun v ↦ ((v.1.1,v.2.1),v.1.2-v.2.2))) ((h,j),z) ≤
      b * ((p.map Prod.fst) h * (q.map Prod.fst) j) := by
  rw [independent_difference_fiber, pmf_fst q, ← mul_assoc,
    ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun y ↦ mul_le_mul' (hp h (z+y)) le_rfl

def independentJoint {H J A B : Type*} (p : PMF (H × A)) (q : PMF (J × B)) :
    PMF ((H × J) × (A × B)) :=
  (independentPair p q).map fun v ↦ ((v.1.1,v.2.1),(v.1.2,v.2.2))

lemma independentJoint_apply {H J A B : Type*} (p : PMF (H × A)) (q : PMF (J × B))
    (h : H) (j : J) (x : A) (y : B) :
    independentJoint p q ((h,j),(x,y)) = p (h,x) * q (j,y) := by
  classical
  simp only [independentJoint, PMF.map_apply, ENNReal.tsum_prod',
    independentPair_apply, Prod.mk.injEq, ite_and]
  simp_rw [enn_tsum_ite_const]
  simp

lemma independentJoint_fst {H J A B : Type*} (p : PMF (H × A)) (q : PMF (J × B)) :
    (independentJoint p q).map Prod.fst =
      independentPair (p.map Prod.fst) (q.map Prod.fst) := by
  rw [independentJoint, PMF.map_comp]
  exact independentPair_map p q Prod.fst Prod.fst

lemma independentJoint_bound {H J A B : Type*} (p : PMF (H × A)) (q : PMF (J × B))
    (b c : ℝ≥0∞) (hp : ∀ h x, p (h,x) ≤ b * (p.map Prod.fst) h)
    (hq : ∀ j y, q (j,y) ≤ c * (q.map Prod.fst) j) (h : H) (j : J) (x : A) (y : B) :
    independentJoint p q ((h,j),(x,y)) ≤
      (b*c) * ((independentJoint p q).map Prod.fst) (h,j) := by
  rw [independentJoint_apply, independentJoint_fst, independentPair_apply]
  exact (mul_le_mul' (hp h x) (hq j y)).trans_eq (by ring)

lemma joint_region_mass {H X : Type*} (p : PMF (H × X)) (E : Set H) (F : Finset X) :
    p.toOuterMeasure {v | v.1 ∈ E ∧ v.2 ∈ F} =
      ∑' h, if h ∈ E then ∑ x ∈ F, p (h,x) else 0 := by
  classical
  rw [PMF.toOuterMeasure_apply, ENNReal.tsum_prod']
  apply tsum_congr
  intro h
  by_cases he : h ∈ E
  · simp only [Set.indicator, Set.mem_ofPred_eq, he, true_and]
    rw [tsum_eq_sum (s := F) (fun x hx ↦ ite_eq_right hx)]
    exact Finset.sum_congr rfl (fun x hx ↦ ite_eq_left hx)
  · simp [Set.indicator, he]

lemma joint_region_bound {H X : Type*} (p : PMF (H × X)) (b : ℝ≥0∞)
    (hp : ∀ h x, p (h,x) ≤ b * (p.map Prod.fst) h) (E : Set H) (F : Finset X) :
    p.toOuterMeasure {v | v.1 ∈ E ∧ v.2 ∈ F} ≤
      (F.card : ℝ≥0∞) * b * (p.map Prod.fst).toOuterMeasure E := by
  classical
  rw [joint_region_mass, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro h
  by_cases he : h ∈ E
  · simp only [he, ite_true, Set.indicator_of_mem]
    calc
      ∑ x ∈ F, p (h,x) ≤ ∑ _x ∈ F, b * (p.map Prod.fst) h :=
        Finset.sum_le_sum fun x _ ↦ hp h x
      _ = _ := by simp [nsmul_eq_mul, mul_assoc]
  · simp [Set.indicator, he]

def timeGaps : {n : ℕ} → (Fin n → ℕ) → Fin n → ℕ
  | 0, _ => Fin.elim0
  | _+1, t => Fin.cases (t 0) (fun i ↦ t i.succ - t i.castSucc)

@[simp] lemma timeGaps_zero {n : ℕ} (t : Fin (n+1) → ℕ) : timeGaps t 0 = t 0 := rfl
@[simp] lemma timeGaps_succ {n : ℕ} (t : Fin (n+1) → ℕ) (i : Fin n) :
    timeGaps t i.succ = t i.succ - t i.castSucc := rfl

lemma timeGaps_castSucc {n : ℕ} (t : Fin (n+1) → ℕ) (i : Fin n) :
    timeGaps t i.castSucc = timeGaps (Fin.init t) i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => exact Fin.cases rfl (fun _ ↦ rfl) i

lemma timeGaps_injective {n : ℕ} :
    Function.Injective (fun t : {t : Fin n → ℕ // Monotone t} ↦ timeGaps t.val) := by
  intro t s h
  apply Subtype.ext
  funext i
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    refine Fin.induction ?_ (fun j ih ↦ ?_) i
    · exact congrFun h 0
    · have he := congrFun h j.succ
      simp only [timeGaps_succ] at he
      have ht := t.property (Fin.castSucc_le_succ j)
      have hs := s.property (Fin.castSucc_le_succ j)
      omega

def splitVectorEquiv (n : ℕ) (A : Type*) : (Fin (n+1) → A) ≃ A × (Fin n → A) where
  toFun f := (f 0, fun i ↦ f i.succ)
  invFun v := Fin.cases v.1 v.2
  left_inv f := by funext i; exact Fin.cases rfl (fun _ ↦ rfl) i
  right_inv v := rfl

lemma tsum_vector_prod {n : ℕ} (f : Fin n → ℕ → ℝ≥0∞) :
    (∑' g : Fin n → ℕ, ∏ i, f i (g i)) = ∏ i, ∑' k, f i k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (splitVectorEquiv n ℕ).symm.tsum_eq]
    change (∑' v : ℕ × (Fin n → ℕ), ∏ i, f i (Fin.cases v.1 v.2 i)) = _
    rw [ENNReal.tsum_prod']
    simp only [Fin.prod_univ_succ, Fin.cases_zero, Fin.cases_succ]
    simp_rw [ENNReal.tsum_mul_left, ih]
    rw [ENNReal.tsum_mul_right]

lemma ordered_gap_sum_bound (T n : ℕ) (b : ℕ → ℝ≥0∞) :
    (∑' t : {t : Fin n → ℕ // StrictMono t ∧ ∀ i, t i ≤ T}, ∏ i, b (timeGaps t.val i)) ≤
      (∑' k, b k)^n := by
  let g : {t : Fin n → ℕ // StrictMono t ∧ ∀ i, t i ≤ T} → (Fin n → ℕ) :=
    fun t ↦ timeGaps t.val
  have hg : Function.Injective g := by
    intro t s he
    have hv := timeGaps_injective (a₁ := ⟨t.val,t.property.1.monotone⟩)
      (a₂ := ⟨s.val,s.property.1.monotone⟩) he
    exact Subtype.ext (congrArg (fun q : {f : Fin n → ℕ // Monotone f} ↦ q.val) hv)
  have h := ENNReal.tsum_comp_le_tsum_of_injective hg (fun v : Fin n → ℕ ↦ ∏ i, b (v i))
  simpa only [g, tsum_vector_prod, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

abbrev BoundedTimes (T n : ℕ) := {t : Fin n → ℕ // StrictMono t ∧ ∀ i, t i ≤ T}
abbrev TimeSubset (T : ℕ) := {s : Finset ℕ // s ∈ (Finset.range (T+1)).powerset}

def encodeTimeSubset (T : ℕ) (s : TimeSubset T) : Σ n, BoundedTimes T n :=
  ⟨s.val.card, ⟨s.val.orderEmbOfFin rfl, (s.val.orderEmbOfFin rfl).strictMono,
    fun i ↦ by
      have h := (Finset.mem_powerset.mp s.property) (s.val.orderEmbOfFin_mem rfl i)
      exact Nat.le_of_lt_succ (Finset.mem_range.mp h)⟩⟩

def decodeTimes {T : ℕ} (v : Σ n, BoundedTimes T n) : Finset ℕ :=
  Finset.univ.image v.2.val

lemma decode_encode (T : ℕ) (s : TimeSubset T) : decodeTimes (encodeTimeSubset T s) = s.val := by
  exact s.val.image_orderEmbOfFin_univ rfl

lemma encodeTimeSubset_injective (T : ℕ) : Function.Injective (encodeTimeSubset T) := by
  intro s t h
  apply Subtype.ext
  simpa only [decode_encode] using congrArg decodeTimes h

lemma prod_encode (T : ℕ) (s : TimeSubset T) (f : ℕ → ℝ≥0∞) :
    (∏ i, f ((encodeTimeSubset T s).2.val i)) = ∏ u ∈ s.val, f u := by
  change (∏ i, f (s.val.orderEmbOfFin rfl i)) = _
  conv_rhs => rw [← s.val.map_orderEmbOfFin_univ rfl, Finset.prod_map]
  rfl

lemma prod_one_add_le_ordered_series (T : ℕ) (f : ℕ → ℝ≥0∞) :
    (∏ u ∈ Finset.range (T+1), (1+f u)) ≤
      ∑' n, ∑' t : BoundedTimes T n, ∏ i, f (t.val i) := by
  rw [Finset.prod_one_add]
  calc
    _ = ∑' s : TimeSubset T, ∏ u ∈ s.val, f u := by
      rw [tsum_fintype]
      exact (Finset.sum_attach _ _).symm
    _ = ∑' s : TimeSubset T, ∏ i, f ((encodeTimeSubset T s).2.val i) := by
      apply tsum_congr
      intro s
      exact (prod_encode T s f).symm
    _ ≤ ∑' v : Σ n, BoundedTimes T n, ∏ i, f (v.2.val i) :=
      ENNReal.tsum_comp_le_tsum_of_injective (encodeTimeSubset_injective T)
        (fun v : Σ n, BoundedTimes T n ↦ ∏ i, f (v.2.val i))
    _ = _ := ENNReal.tsum_sigma' _

abbrev PairNoise (m : ℕ) := TreeNoise m × TreeNoise m
abbrev FourNoise (m : ℕ) := PairNoise m × PairNoise m
abbrev PairHistory (u : ℕ) := (Fin (u+1) → ℤ) × (Fin (u+1) → ℤ)
abbrev FourHistory (u : ℕ) := PairHistory u × PairHistory u

def pairLaw (m : ℕ) : PMF (PairNoise m) :=
  independentPair (PMF.uniformOfFintype (TreeNoise m)) (PMF.uniformOfFintype (TreeNoise m))

def fourLaw (m : ℕ) : PMF (FourNoise m) := independentPair (pairLaw m) (pairLaw m)

end HardSphere.Lattice
end

end OAI
