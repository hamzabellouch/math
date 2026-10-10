import OAI.Geometry.UnitDistances.Predictions

namespace OAI

namespace PlanarUnitDistances.TripleCoupling
open Finset FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q H : Type*} [Fintype P] [Fintype Q] [Fintype H]

abbrev Outcome (P Q : Type*) := P×(P×(Q×(Q×Q)))

def law (π : Law (P×Q)) (h : P → H) : Law (Outcome P Q) :=
  dependent (left π) (fun p => pair (cond (left π) h (h p)) (triple (row π p)))

def point (a : Outcome P Q) : P := a.1
def prediction (a : Outcome P Q) : P := a.2.1
def neighbor (a : Outcome P Q) (i : Fin 3) : Q := entry a.2.2 i

omit [Fintype H] in
lemma first (π : Law (P×Q)) (h : P → H) (f : P → ℝ) :
    avg (law π h) (fun a => f (point a))=avg (left π) f := by
  simp only [law,dependent_avg,point,avg_const]

lemma predicted_point (π : Law (P×Q)) (h : P → H) (f : P → ℝ) :
    avg (law π h) (fun a => f (prediction a))=avg (left π) f := by
  simp only [law,dependent_avg,prediction,pair_avg,avg_const]
  rw [←push_avg (left π) h (fun j => avg (cond (left π) h j) f)]
  exact cond_tower (left π) h f

omit [Fintype H] in
lemma edge (π : Law (P×Q)) (h : P → H) (i : Fin 3) (f : P → Q → ℝ) :
    avg (law π h) (fun a => f (point a) (neighbor a i))=avg π (fun pq => f pq.1 pq.2) := by
  simp only [law,dependent_avg,point,neighbor,pair_avg,triple_coordinate,avg_const]
  exact row_avg π f

omit [Fintype H] in
lemma center (π : Law (P×Q)) (h : P → H) (i : Fin 3) (f : Q → ℝ) :
    avg (law π h) (fun a => f (neighbor a i))=avg (right π) f := by
  simpa only [right,push_avg] using edge π h i (fun _ q => f q)

omit [Fintype H] in
lemma predicted_pair (π : Law (P×Q)) (h : P → H) (i : Fin 3) (f : P → Q → ℝ) :
    avg (law π h) (fun a => f (prediction a) (neighbor a i))=
      avg (right π) (fun q => avg (col π q) (fun p =>
        avg (cond (left π) h (h p)) (fun r => f r q))) := by
  simp only [law,dependent_avg,prediction,neighbor,pair_avg,triple_coordinate]
  simp_rw [avg_comm (cond (left π) h (h _)) (row π _)]
  rw [row_avg,col_avg]

lemma point_prediction (π : Law (P×Q)) (h : P → H) (f : P → P → ℝ) :
    avg (law π h) (fun a => f (point a) (prediction a))=
      avg (PredictionCoupling.coupling (left π) h) (fun pp => f pp.1 pp.2) := by
  simp only [law,dependent_avg,point,prediction,pair_avg,avg_const,
    PredictionCoupling.coupling,mix_avg]
  exact (cond_tower_dep (left π) h (fun j p => avg (cond (left π) h j) (f p))).symm

omit [Fintype H] in
lemma two_centers (π : Law (P×Q)) (h : P → H) (i j : Fin 3) (f : Q → Q → ℝ) :
    avg (law π h) (fun a => f (neighbor a i) (neighbor a j))=
      avg (left π) (fun p => avg (triple (row π p)) (fun x => f (entry x i) (entry x j))) := by
  simp only [law,dependent_avg,neighbor,pair_avg,avg_const]

lemma predicted_diagonal (π : Law (P×Q)) (h : P → H) {d : ℝ}
    (hd : 0 ≤ d) (hm : ∀p,(left π).val p ≤ d) :
    event (law π h) (fun a => point a=prediction a) ≤ (Fintype.card H:ℝ)*d := by
  change avg (law π h) (fun a => (fun p r => if p=r then (1:ℝ) else 0) (point a) (prediction a))≤_
  rw [point_prediction π h (fun p r => if p=r then (1:ℝ) else 0)]
  exact PredictionCoupling.diagonal (left π) h hd hm

omit [Fintype H] in
lemma center_diagonal (π : Law (P×Q)) (h : P → H) (i j : Fin 3) (hij : i≠j)
    {d : ℝ} (hm : ∀p q,(row π p).val q ≤ d) :
    event (law π h) (fun a => neighbor a i=neighbor a j) ≤ d := by
  change avg (law π h) (fun a => (fun q r => if q=r then (1:ℝ) else 0) (neighbor a i) (neighbor a j))≤_
  rw [two_centers π h i j (fun q r => if q=r then (1:ℝ) else 0)]
  change avg (left π) (fun p => event (triple (row π p))
    (fun x => entry x i=entry x j)) ≤ d
  simp_rw [triple_collision _ i j hij]
  exact avg_le_const _ (fun p => collision_le_atom (row π p) (hm p))
end
end PlanarUnitDistances.TripleCoupling

namespace PlanarUnitDistances.FiniteQuantization
open scoped Classical
noncomputable section

def radius (B τ : ℝ) : ℕ := ⌈B/τ⌉₊
abbrev Cell (B τ : ℝ) := ↥(Finset.Icc (-(radius B τ : ℤ)) (radius B τ : ℤ))
abbrev Axis (B τ : ℝ) := Option (Cell B τ)
abbrev Alphabet (B τ : ℝ) := (Axis B τ×Axis B τ)×(Axis B τ×Axis B τ)

def axis (B τ x : ℝ) : Axis B τ :=
  if h : ⌊x/τ⌋ ∈ Finset.Icc (-(radius B τ : ℤ)) (radius B τ : ℤ) then
    some ⟨⌊x/τ⌋,h⟩ else none

def code (B τ : ℝ) (Z W : ℂ) : Alphabet B τ :=
  ((axis B τ Z.re,axis B τ Z.im),(axis B τ W.re,axis B τ W.im))

lemma bounded_cell {B τ x : ℝ} (hτ : 0 < τ) (hx : |x| ≤ B) :
    ⌊x/τ⌋ ∈ Finset.Icc (-(radius B τ : ℤ)) (radius B τ : ℤ) := by
  have hN : B/τ ≤ (radius B τ : ℝ) := Nat.le_ceil _
  have hu : x/τ ≤ (radius B τ : ℝ) :=
    (div_le_div_of_nonneg_right (le_trans (le_abs_self x) hx) hτ.le).trans hN
  have hl : -(radius B τ : ℝ) ≤ x/τ := by
    have hh : -B ≤ x := (abs_le.mp hx).1
    have hh' := div_le_div_of_nonneg_right hh hτ.le
    rw [neg_div] at hh'
    linarith
  apply Finset.mem_Icc.mpr
  constructor
  · apply Int.le_floor.mpr
    simpa only [Int.cast_neg,Int.cast_natCast] using hl
  · apply Int.floor_le_iff.mpr
    simp only [Int.cast_natCast]
    linarith

lemma axis_close {B τ x y : ℝ} (hτ : 0 < τ) (hx : |x| ≤ B)
    (he : axis B τ x=axis B τ y) : |y-x| < τ := by
  have hmem := bounded_cell hτ hx
  have hf : ⌊x/τ⌋=⌊y/τ⌋ := by
    unfold axis at he
    rw [dite_eq_left hmem] at he
    split_ifs at he with hy
    · exact congrArg Subtype.val (Option.some.inj he)
  have hx0 := Int.floor_le (x/τ)
  have hx1 := Int.lt_floor_add_one (x/τ)
  have hy0 := Int.floor_le (y/τ)
  have hy1 := Int.lt_floor_add_one (y/τ)
  rw [←hf] at hy0 hy1
  have h1 : (y-x)/τ < 1 := by rw [sub_div]; linarith
  have h2 : (x-y)/τ < 1 := by rw [sub_div]; linarith
  have h1' := (div_lt_iff₀ hτ).mp h1
  have h2' := (div_lt_iff₀ hτ).mp h2
  apply abs_lt.mpr
  constructor <;> linarith

lemma complex_close {B τ : ℝ} {z z' : ℂ} (hτ : 0 < τ) (hz : ‖z‖ ≤ B)
    (he : (axis B τ z.re,axis B τ z.im)=(axis B τ z'.re,axis B τ z'.im)) :
    ‖z'-z‖ ≤ Real.sqrt 2*τ := by
  have hr := (axis_close hτ ((Complex.abs_re_le_norm z).trans hz) (congrArg Prod.fst he)).le
  have hi := (axis_close hτ ((Complex.abs_im_le_norm z).trans hz) (congrArg Prod.snd he)).le
  have hr2 := mul_self_le_mul_self (abs_nonneg (z'.re-z.re)) hr
  have hi2 := mul_self_le_mul_self (abs_nonneg (z'.im-z.im)) hi
  simp only [←pow_two, sq_abs] at hr2 hi2
  have hn := Complex.sq_norm (z'-z)
  rw [Complex.normSq_apply] at hn
  simp only [Complex.sub_re,Complex.sub_im] at hn
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp : 0 ≤ Real.sqrt 2*τ := mul_nonneg (Real.sqrt_nonneg _) hτ.le
  nlinarith [norm_nonneg (z'-z)]

theorem same_code_close {B τ : ℝ} (hτ : 0 < τ) {Z W Z' W' : ℂ}
    (hZ : ‖Z‖ ≤ B) (hW : ‖W‖ ≤ B) (he : code B τ Z W=code B τ Z' W') :
    ‖Z'-Z‖ ≤ Real.sqrt 2*τ ∧ ‖W'-W‖ ≤ Real.sqrt 2*τ := by
  exact ⟨complex_close hτ hZ (congrArg Prod.fst he),
    complex_close hτ hW (congrArg Prod.snd he)⟩

lemma alphabet_card (B τ : ℝ) : Fintype.card (Alphabet B τ)=(2*radius B τ+2)^4 := by
  have hc : Fintype.card (Cell B τ)=2*radius B τ+1 := by
    rw [Fintype.card_coe,Int.card_Icc]
    omega
  simp only [Alphabet,Fintype.card_prod,Axis,Fintype.card_option,hc]
  ring
end
end PlanarUnitDistances.FiniteQuantization

namespace PlanarUnitDistances.BoundedScaleGeometry

lemma inverse_difference_det {K : Type*} [Field K] (d₀ d₁ d₂ : K)
    (h₀ : d₀ ≠ 0) (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) :
    ((d₁⁻¹-d₀⁻¹)*(d₂-d₀)-(d₂⁻¹-d₀⁻¹)*(d₁-d₀))*d₀*d₁*d₂ =
      (d₀-d₁)*(d₀-d₂)*(d₁-d₂) := by
  field_simp
  ring

lemma cramer_identity {K : Type*} [Field K] (d₀ d₁ d₂ z w E₀ E₁ E₂ : K)
    (he₀ : z/d₀ + w*d₀ + z*w = E₀)
    (he₁ : z/d₁ + w*d₁ + z*w = E₁)
    (he₂ : z/d₂ + w*d₂ + z*w = E₂) :
    ((d₁⁻¹-d₀⁻¹)*(d₂-d₀)-(d₂⁻¹-d₀⁻¹)*(d₁-d₀))*z =
      (E₁-E₀)*(d₂-d₀)-(E₂-E₀)*(d₁-d₀) := by
  simp only [div_eq_mul_inv] at he₀ he₁ he₂
  linear_combination (d₂-d₀)*(he₁-he₀)-(d₁-d₀)*(he₂-he₀)

lemma quantized_edge_error (Z W Z' W' a b : ℂ) {B τ : ℝ}
    (_hB : 0 ≤ B) (hτ : 0 ≤ τ)
    (hZ : ‖Z‖ ≤ B) (hW : ‖W‖ ≤ B) (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B)
    (hZ' : ‖Z'-Z‖ ≤ τ) (hW' : ‖W'-W‖ ≤ τ)
    (he : (Z'-a)*(W'-b) = 1) :
    ‖(Z-a)*(W-b)-1‖ ≤ 4*B*τ + τ^2 := by
  have hid : (Z-a)*(W-b)-1 =
      -(Z'-Z)*(W-b)-(W'-W)*(Z-a)-(Z'-Z)*(W'-W) := by
    linear_combination he
  rw [hid]
  calc
    _ ≤ ‖-(Z'-Z)*(W-b)-(W'-W)*(Z-a)‖+‖(Z'-Z)*(W'-W)‖ := norm_sub_le _ _
    _ ≤ ‖-(Z'-Z)*(W-b)‖+‖(W'-W)*(Z-a)‖+‖(Z'-Z)*(W'-W)‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ τ*(B+B)+τ*(B+B)+τ*τ := by
      simp only [norm_mul, norm_neg]
      gcongr
      · exact (norm_sub_le _ _).trans (add_le_add hW hb)
      · exact (norm_sub_le _ _).trans (add_le_add hZ ha)
    _ = _ := by ring

lemma square_grid_edge_error (Z W Z' W' a b : ℂ) {B τ : ℝ}
    (hB : 2 ≤ B) (hτ : 0 ≤ τ) (hτ₁ : τ ≤ 1)
    (hZ : ‖Z‖ ≤ B) (hW : ‖W‖ ≤ B) (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B)
    (hZ' : ‖Z'-Z‖ ≤ Real.sqrt 2 * τ) (hW' : ‖W'-W‖ ≤ Real.sqrt 2 * τ)
    (he : (Z'-a)*(W'-b) = 1) :
    ‖(Z-a)*(W-b)-1‖ ≤ 8*B*τ := by
  have hs : Real.sqrt 2 ≤ (3:ℝ)/2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2:ℝ)]
  have hBn : 0 ≤ B := by linarith
  calc
    _ ≤ 4*B*(Real.sqrt 2*τ)+(Real.sqrt 2*τ)^2 :=
      quantized_edge_error Z W Z' W' a b hBn (by positivity) hZ hW ha hb hZ' hW' he
    _ = 4*B*(Real.sqrt 2*τ)+2*τ^2 := by
      rw [mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
    _ ≤ 6*B*τ+2*τ := by
      have h₁ := mul_le_mul_of_nonneg_right hs (show 0 ≤ 4*B*τ by positivity)
      have h₂ : τ^2 ≤ τ := by nlinarith
      nlinarith
    _ ≤ 8*B*τ := by nlinarith [mul_nonneg (show 0 ≤ B-1 by linarith) hτ]

theorem no_separated_approximate_point
    (d₀ d₁ d₂ z w E₀ E₁ E₂ : ℂ) {B r τ : ℝ}
    (hB : 0 < B) (hr : 0 < r) (hτ : 0 ≤ τ)
    (h₀ : d₀ ≠ 0) (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0)
    (hd₀ : ‖d₀‖ ≤ B) (hd₁ : ‖d₁‖ ≤ B) (hd₂ : ‖d₂‖ ≤ B)
    (hs₀₁ : r ≤ ‖d₀-d₁‖) (hs₀₂ : r ≤ ‖d₀-d₂‖) (hs₁₂ : r ≤ ‖d₁-d₂‖)
    (hz : r ≤ ‖z‖)
    (hE₀ : ‖E₀‖ ≤ 8*B*τ) (hE₁ : ‖E₁‖ ≤ 8*B*τ) (hE₂ : ‖E₂‖ ≤ 8*B*τ)
    (he₀ : z/d₀ + w*d₀ + z*w = E₀)
    (he₁ : z/d₁ + w*d₁ + z*w = E₁)
    (he₂ : z/d₂ + w*d₂ + z*w = E₂)
    (hmesh : τ < r^4/(128*B^5)) : False := by
  let Δ := (d₁⁻¹-d₀⁻¹)*(d₂-d₀)-(d₂⁻¹-d₀⁻¹)*(d₁-d₀)
  have hdet : ‖Δ‖*B^3 ≥ r^3 := by
    have hh := congrArg norm (inverse_difference_det d₀ d₁ d₂ h₀ h₁ h₂)
    simp only [norm_mul] at hh
    calc
      r^3 = r*r*r := by ring
      _ ≤ ‖d₀-d₁‖*‖d₀-d₂‖*‖d₁-d₂‖ := by gcongr
      _ = ‖Δ‖*‖d₀‖*‖d₁‖*‖d₂‖ := hh.symm
      _ ≤ ‖Δ‖*B*B*B := by gcongr
      _ = ‖Δ‖*B^3 := by ring
  have hup : ‖Δ‖*‖z‖ ≤ 64*B^2*τ := by
    have hh := congrArg norm (cramer_identity d₀ d₁ d₂ z w E₀ E₁ E₂ he₀ he₁ he₂)
    rw [norm_mul] at hh
    change ‖Δ‖*‖z‖ = _ at hh
    rw [hh]
    calc
      _ ≤ ‖(E₁-E₀)*(d₂-d₀)‖+‖(E₂-E₀)*(d₁-d₀)‖ := norm_sub_le _ _
      _ = ‖E₁-E₀‖*‖d₂-d₀‖+‖E₂-E₀‖*‖d₁-d₀‖ := by simp only [norm_mul]
      _ ≤ (16*B*τ)*(2*B)+(16*B*τ)*(2*B) := by
        gcongr
        · exact (norm_sub_le _ _).trans (by linarith)
        · exact (norm_sub_le _ _).trans (by linarith)
        · exact (norm_sub_le _ _).trans (by linarith)
        · exact (norm_sub_le _ _).trans (by linarith)
      _ = _ := by ring
  have hfinal : r^4 ≤ 64*B^5*τ := by
    calc
      r^4 = r^3*r := by ring
      _ ≤ (‖Δ‖*B^3)*‖z‖ := mul_le_mul hdet hz hr.le (by positivity)
      _ = (‖Δ‖*‖z‖)*B^3 := by ring
      _ ≤ (64*B^2*τ)*B^3 := mul_le_mul_of_nonneg_right hup (by positivity)
      _ = _ := by ring
  have hm := (lt_div_iff₀ (show 0 < 128*B^5 by positivity)).mp hmesh
  nlinarith [pow_pos hr 4]
end PlanarUnitDistances.BoundedScaleGeometry

namespace PlanarUnitDistances.QuantizedContradiction
open FiniteQuantization BoundedScaleGeometry
open scoped Classical
noncomputable section

lemma difference_equation (Z W R S a b : ℂ) (he : (Z-a)*(W-b)=1) :
    (R-Z)/(Z-a)+(S-W)*(Z-a)+(R-Z)*(S-W)=(R-a)*(S-b)-1 := by
  have hi : (Z-a)⁻¹=W-b := inv_eq_of_mul_eq_one_right he
  rw [div_eq_mul_inv,hi]
  linear_combination -he

theorem impossible {P Q : Type*} (Z W : P → ℂ) (a b : Q → ℂ) (E : P → Q → Prop)
    (unit : ∀p q,E p q → (Z p-a q)*(W p-b q)=1)
    (p r : P) (q : Fin 3 → Q) {B τ δ : ℝ}
    (hB : 2 ≤ B) (hτ : 0 < τ) (hτ₁ : τ ≤ 1) (hδ : 0 < δ)
    (hmesh : τ < δ^4/(128*B^5))
    (hp : ∀i,E p (q i))
    (hr : ∀i,∃s,E s (q i) ∧ code B τ (Z r) (W r)=code B τ (Z s) (W s))
    (hZ : ‖Z r‖ ≤ B) (hW : ‖W r‖ ≤ B)
    (ha : ∀i,‖a (q i)‖ ≤ B) (hb : ∀i,‖b (q i)‖ ≤ B)
    (hd : ∀i,‖Z p-a (q i)‖ ≤ B)
    (hsep : ∀i j : Fin 3,i<j → δ ≤ ‖(Z p-a (q i))-(Z p-a (q j))‖)
    (hpr : δ ≤ ‖Z r-Z p‖) : False := by
  let d : Fin 3 → ℂ := fun i => Z p-a (q i)
  let F : Fin 3 → ℂ := fun i => (Z r-a (q i))*(W r-b (q i))-1
  have hdn (i : Fin 3) : d i ≠ 0 := by
    have hh := unit p (q i) (hp i)
    intro hz
    change Z p-a (q i)=0 at hz
    rw [hz,zero_mul] at hh
    exact zero_ne_one hh
  have hF (i : Fin 3) : ‖F i‖ ≤ 8*B*τ := by
    obtain ⟨s,hs,hc⟩ := hr i
    obtain ⟨hcZ,hcW⟩ := same_code_close hτ hZ hW hc
    exact square_grid_edge_error (Z r) (W r) (Z s) (W s) (a (q i)) (b (q i))
      hB hτ.le hτ₁ hZ hW (ha i) (hb i) hcZ hcW (unit s (q i) hs)
  have he (i : Fin 3) : (Z r-Z p)/d i+(W r-W p)*d i+(Z r-Z p)*(W r-W p)=F i :=
    difference_equation (Z p) (W p) (Z r) (W r) (a (q i)) (b (q i)) (unit p (q i) (hp i))
  exact no_separated_approximate_point (d 0) (d 1) (d 2) (Z r-Z p) (W r-W p)
    (F 0) (F 1) (F 2) (by linarith) hδ hτ.le (hdn 0) (hdn 1) (hdn 2)
    (hd 0) (hd 1) (hd 2) (hsep 0 1 (by decide)) (hsep 0 2 (by decide))
    (hsep 1 2 (by decide)) hpr (hF 0) (hF 1) (hF 2) (he 0) (he 1) (he 2) hmesh
end
end PlanarUnitDistances.QuantizedContradiction

namespace PlanarUnitDistances.BoundedGeometricCover
open FiniteLaw FiniteStarCoupling TripleCoupling FiniteQuantization
open scoped Classical
noncomputable section
variable {P Q K : Type*} [Field K] [NumberField K]

abbrev BigIndex := Bool ⊕ (Fin 3 × (Bool ⊕ Unit))
abbrev SmallIndex := Unit ⊕ (Fin 3 × Fin 3)

def big (Z W : P → K) (a b : Q → K) (x : Outcome P Q) : BigIndex → K
  | .inl false => Z (prediction x)
  | .inl true => W (prediction x)
  | .inr (i,.inl false) => a (neighbor x i)
  | .inr (i,.inl true) => b (neighbor x i)
  | .inr (i,.inr ()) => Z (point x)-a (neighbor x i)

def small (Z : P → K) (a : Q → K) (x : Outcome P Q) : SmallIndex → K
  | .inl () => Z (prediction x)-Z (point x)
  | .inr (i,j) => (Z (point x)-a (neighbor x i))-(Z (point x)-a (neighbor x j))

def accept (Z W : P → K) (E : P → Q → Prop) (B τ : ℝ) (σ : K →ₐ[ℚ] ℂ)
    (r : P) (q : Q) : Prop :=
  ∃s,E s q ∧ code B τ (σ (Z r)) (σ (W r))=code B τ (σ (Z s)) (σ (W s))

def bad (Z W : P → K) (a b : Q → K) (E : P → Q → Prop) (B τ δ : ℝ) :
    Fin 6 → (Outcome P Q × (K →ₐ[ℚ] ℂ)) → Prop
  | 0,x => ∃i,B < ‖x.2 (big Z W a b x.1 i)‖
  | 1,x => ∃i,small Z a x.1 i ≠ 0 ∧ ‖x.2 (small Z a x.1 i)‖ < δ
  | 2,x => point x.1=prediction x.1
  | 3,x => ∃ij : Fin 3 × Fin 3,ij.1 < ij.2 ∧ neighbor x.1 ij.1=neighbor x.1 ij.2
  | 4,x => ∃i,¬E (point x.1) (neighbor x.1 i)
  | 5,x => ∃i,¬accept Z W E B τ x.2 (prediction x.1) (neighbor x.1 i)

theorem cover (Z W : P → K) (a b : Q → K) (E : P → Q → Prop)
    (hu : ∀p q,E p q → (Z p-a q)*(W p-b q)=1)
    (hZinj : Function.Injective Z) (hainj : Function.Injective a)
    {B τ δ : ℝ} (hB : 2 ≤ B) (hτ : 0 < τ) (hτ₁ : τ ≤ 1) (hδ : 0 < δ)
    (hmesh : τ < δ^4/(128*B^5)) (x : Outcome P Q × (K →ₐ[ℚ] ℂ)) :
    ∃i,bad Z W a b E B τ δ i x := by
  by_contra hn
  have hh (i : Fin 6) : ¬bad Z W a b E B τ δ i x := fun hi => hn ⟨i,hi⟩
  have hb (i : BigIndex) : ‖x.2 (big Z W a b x.1 i)‖ ≤ B :=
    le_of_not_gt (fun hi => hh 0 ⟨i,hi⟩)
  have hs (i : SmallIndex) (hi : small Z a x.1 i ≠ 0) : δ ≤ ‖x.2 (small Z a x.1 i)‖ :=
    le_of_not_gt (fun hz => hh 1 ⟨i,hi,hz⟩)
  have hp : point x.1 ≠ prediction x.1 := hh 2
  have hq (i j : Fin 3) (hij : i < j) : neighbor x.1 i ≠ neighbor x.1 j :=
    fun he => hh 3 ⟨(i,j),hij,he⟩
  have he (i : Fin 3) : E (point x.1) (neighbor x.1 i) := by
    by_contra hi
    exact hh 4 ⟨i,hi⟩
  have ha (i : Fin 3) : accept Z W E B τ x.2 (prediction x.1) (neighbor x.1 i) := by
    by_contra hi
    exact hh 5 ⟨i,hi⟩
  have hsep (i j : Fin 3) (hij : i < j) :
      δ ≤ ‖(x.2 (Z (point x.1))-x.2 (a (neighbor x.1 i)))-
        (x.2 (Z (point x.1))-x.2 (a (neighbor x.1 j)))‖ := by
    have hi : small Z a x.1 (.inr (i,j)) ≠ 0 := by
      simp only [small,sub_ne_zero]
      intro h
      exact hq i j hij (hainj (sub_right_inj.mp h))
    simpa only [small,map_sub] using hs (.inr (i,j)) hi
  have hpr : δ ≤ ‖x.2 (Z (prediction x.1))-x.2 (Z (point x.1))‖ := by
    have hi : small Z a x.1 (.inl ()) ≠ 0 := by
      rw [small,sub_ne_zero]
      exact fun h => hp (hZinj h).symm
    simpa only [small,map_sub] using hs (.inl ()) hi
  exact QuantizedContradiction.impossible (fun p => x.2 (Z p)) (fun p => x.2 (W p))
    (fun q => x.2 (a q)) (fun q => x.2 (b q)) E
    (fun p q h => by simpa only [map_mul,map_sub,map_one] using congrArg x.2 (hu p q h))
    (point x.1) (prediction x.1) (neighbor x.1) hB hτ hτ₁ hδ hmesh he ha
    (hb (.inl false)) (hb (.inl true)) (fun i => hb (.inr (i,.inl false)))
    (fun i => hb (.inr (i,.inl true)))
    (fun i => by simpa only [big,map_sub] using hb (.inr (i,.inr ()))) hsep hpr
end
end PlanarUnitDistances.BoundedGeometricCover

namespace PlanarUnitDistances.BoundedProbabilities
open Finset FiniteLaw FiniteStarCoupling TripleCoupling BoundedGeometricCover
open WeightedAbsoluteValues EmbeddingTails
open scoped Classical
noncomputable section
variable {P Q H K : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Field K] [NumberField K] [IsGalois ℚ K]

omit [Fintype P] [Fintype Q] [Fintype H] in
lemma height_sub (x y : K) : exactHeight K (x-y) ≤ exactHeight K x+exactHeight K y+Real.log 2 := by
  have hh := exactHeight_add_le K x (-y)
  rw [←sub_eq_add_neg,exactHeight_neg] at hh
  linarith

omit [IsGalois ℚ K] in
lemma big_mean (π : Law (P×Q)) (h : P → H) (Z W : P → K) (a b : Q → K)
    {C : ℝ} (hZ : avg (left π) (fun p => exactHeight K (Z p)) ≤ C)
    (hW : avg (left π) (fun p => exactHeight K (W p)) ≤ C)
    (ha : avg (right π) (fun q => exactHeight K (a q)) ≤ C)
    (hb : avg (right π) (fun q => exactHeight K (b q)) ≤ C)
    (hD : avg π (fun pq => exactHeight K (Z pq.1-a pq.2)) ≤ C) (i : BigIndex) :
    avg (law π h) (fun x => exactHeight K (big Z W a b x i)) ≤ C := by
  rcases i with i | ⟨j,i⟩
  · cases i
    · exact (predicted_point π h (fun p => exactHeight K (Z p))).le.trans hZ
    · exact (predicted_point π h (fun p => exactHeight K (W p))).le.trans hW
  · rcases i with i | i
    · cases i
      · exact (center π h j (fun q => exactHeight K (a q))).le.trans ha
      · exact (center π h j (fun q => exactHeight K (b q))).le.trans hb
    · cases i
      exact (edge π h j (fun p q => exactHeight K (Z p-a q))).le.trans hD

lemma small_mean (π : Law (P×Q)) (h : P → H) (Z : P → K) (a : Q → K)
    {C : ℝ} (hZ : avg (left π) (fun p => exactHeight K (Z p)) ≤ C)
    (ha : avg (right π) (fun q => exactHeight K (a q)) ≤ C) (i : SmallIndex) :
    avg (law π h) (fun x => exactHeight K (BoundedGeometricCover.small Z a x i)) ≤ 2*C+Real.log 2 := by
  rcases i with i | ⟨i,j⟩
  · cases i
    have hh:=avg_mono (law π h) (fun x => height_sub (Z (prediction x)) (Z (point x)))
    simp only [avg_add,avg_const] at hh
    rw [predicted_point π h (fun p => exactHeight K (Z p)),
      first π h (fun p => exactHeight K (Z p))] at hh
    exact hh.trans (by linarith)
  · have hs (x : Outcome P Q) : BoundedGeometricCover.small Z a x (.inr (i,j))=a (neighbor x j)-a (neighbor x i) := by
      simp only [BoundedGeometricCover.small]; ring
    have hh:=avg_mono (law π h) (fun x => height_sub (a (neighbor x j)) (a (neighbor x i)))
    simp only [avg_add,avg_const] at hh
    rw [center π h j (fun q => exactHeight K (a q)),center π h i (fun q => exactHeight K (a q))] at hh
    simp_rw [hs]
    exact hh.trans (by linarith)

omit [Fintype H] in
lemma large_bound (π : Law (P×Q)) (h : P → H) (Z W : P → K) (a b : Q → K)
    {C B τ δ : ℝ} (hB : 1 < B) (E : P → Q → Prop)
    (hmean : ∀i,avg (law π h) (fun x => exactHeight K (big Z W a b x i)) ≤ C) :
    event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 0) ≤ 11*C/Real.log B := by
  have hh := large_family (law π h) (fun i x => big Z W a b x i) hB
  refine hh.trans (div_le_div_of_nonneg_right ?_ (Real.log_pos hB).le)
  rw [avg_sum]
  calc
    _ ≤ ∑ _ : BigIndex,C := sum_le_sum (fun i _ => hmean i)
    _ = 11*C := by norm_num [BigIndex]

omit [Fintype H] in
lemma small_bound (π : Law (P×Q)) (h : P → H) (Z W : P → K) (a b : Q → K)
    {C B τ δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) (E : P → Q → Prop)
    (hmean : ∀i,avg (law π h) (fun x => exactHeight K (BoundedGeometricCover.small Z a x i)) ≤ C) :
    event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 1) ≤ 10*C/Real.log (1/δ) := by
  have hh := small_family (law π h) (fun i x => small Z a x i) hδ hδ₁
  refine hh.trans (div_le_div_of_nonneg_right ?_ (Real.log_pos ((one_lt_div hδ).mpr hδ₁)).le)
  rw [avg_sum]
  calc
    _ ≤ ∑ _ : SmallIndex,C := sum_le_sum (fun i _ => hmean i)
    _ = 10*C := by norm_num [SmallIndex]

lemma point_bound (π : Law (P×Q)) (h : P → H) (Z W : P → K) (a b : Q → K)
    (E : P → Q → Prop) (B τ δ : ℝ) {d : ℝ} (hd : 0 ≤ d)
    (hm : ∀p,(left π).val p ≤ d) :
    event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 2) ≤ (Fintype.card H:ℝ)*d := by
  have he : event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 2)=
      event (law π h) (fun x => point x=prediction x) := by
    unfold event
    rw [pair_avg]
    apply avg_congr
    intro x
    by_cases hx : point x=prediction x <;>
      simp only [BoundedGeometricCover.bad,hx,ite_true,ite_false,avg_const]
  rw [he]
  exact predicted_diagonal π h hd hm

omit [Fintype H] in
lemma centers_bound (π : Law (P×Q)) (h : P → H) (Z W : P → K) (a b : Q → K)
    (E : P → Q → Prop) (B τ δ : ℝ) {d : ℝ} (hd : 0 ≤ d)
    (hm : ∀p q,(row π p).val q ≤ d) :
    event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 3) ≤ 9*d := by
  have he : event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 3)=
      event (law π h) (fun x => ∃ij : Fin 3×Fin 3,ij.1 < ij.2 ∧ neighbor x ij.1=neighbor x ij.2) := by
    unfold event
    rw [pair_avg]
    apply avg_congr
    intro x
    by_cases hx : ∃ij : Fin 3×Fin 3,ij.1 < ij.2 ∧ neighbor x ij.1=neighbor x ij.2 <;>
      simp only [BoundedGeometricCover.bad,hx,ite_true,ite_false,avg_const]
  rw [he]
  refine (event_exists_le (law π h) _).trans ?_
  calc
    _ ≤ ∑ _ : Fin 3 × Fin 3,d := by
      apply sum_le_sum
      intro ij _
      by_cases hij : ij.1 < ij.2
      · refine (event_mono _ (fun _ hx => hx.2)).trans (center_diagonal π h ij.1 ij.2 (ne_of_lt hij) hm)
      · simpa only [hij,false_and,event_false] using hd
    _ = 9*d := by norm_num

omit [Fintype H] in
lemma nonedge_zero (π : Law (P×Q)) (h : P → H) (Z W : P → K) (a b : Q → K)
    (E : P → Q → Prop) (hE : ∀p q,0 < π.val (p,q) → E p q) (B τ δ : ℝ) :
    event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 4) ≤ 0 := by
  have he : event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 4)=
      event (law π h) (fun x => ∃i,¬E (point x) (neighbor x i)) := by
    unfold event
    rw [pair_avg]
    apply avg_congr
    intro x
    by_cases hx : ∃i,¬E (point x) (neighbor x i) <;>
      simp only [BoundedGeometricCover.bad,hx,ite_true,ite_false,avg_const]
  rw [he]
  refine (event_exists_le (law π h) _).trans ?_
  apply sum_nonpos
  intro i _
  have hi : event (law π h) (fun x => ¬E (point x) (neighbor x i))=
      event π (fun pq => ¬E pq.1 pq.2) := by
    simpa only [avg_ite] using edge π h i (fun p q => if ¬E p q then (1:ℝ) else 0)
  rw [hi]
  unfold event avg
  apply sum_nonpos
  intro pq _
  by_cases hpos : 0 < π.val pq
  · simp [hE pq.1 pq.2 hpos]
  · have hz := le_antisymm (le_of_not_gt hpos) (π.nonneg pq)
    simp [hz]

omit [Fintype H] in
lemma mixture_col (π : Law (P×Q)) : mixture (right π) (col π)=left π := by
  apply law_ext
  intro p
  simp only [mixture,avg,col_weight,FiniteStarCoupling.left_val]

def failure (π : Law (P×Q)) (h : P → H) (Z W : P → K)
    (E : P → Q → Prop) (B τ : ℝ) : ℝ :=
  avg (uniform (Embeddings K)) (fun σ => avg (right π) (fun q => avg (col π q) (fun p =>
    event (cond (left π) h (h p)) (fun r => ¬accept Z W E B τ σ r q))))

omit [Fintype H] in
lemma failure_bound (π : Law (P×Q)) (h : P → H) (Z W : P → K) (a b : Q → K)
    (E : P → Q → Prop) (B τ δ : ℝ) :
    event (pair (law π h) (uniform (Embeddings K))) (bad Z W a b E B τ δ 5) ≤ 3*failure π h Z W E B τ := by
  refine (event_exists_le _ _).trans ?_
  have he (i : Fin 3) : event (pair (law π h) (uniform (Embeddings K)))
      (fun x => ¬accept Z W E B τ x.2 (prediction x.1) (neighbor x.1 i)) = failure π h Z W E B τ := by
    rw [event,pair_avg,avg_comm]
    unfold failure
    apply avg_congr
    intro σ
    calc
      _ = event (law π h) (fun x => ¬accept Z W E B τ σ (prediction x) (neighbor x i)) := by
        unfold event
        apply avg_congr
        intro x
        split_ifs <;> simp_all only [not_true_eq_false,not_false_eq_true]
      _ = _ := by
        simpa only [avg_ite] using predicted_pair π h i (fun r q => if ¬accept Z W E B τ σ r q then (1:ℝ) else 0)
  simp only [he,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,le_refl]
end
end PlanarUnitDistances.BoundedProbabilities

end OAI
