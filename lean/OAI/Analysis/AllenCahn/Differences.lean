import OAI.Analysis.AllenCahn.RegularityModel

namespace OAI

noncomputable section
namespace RegularitySupport.DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
open MeasureTheory
open scoped ENNReal

lemma laplacian_poisson_at_max {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (A ε : ℝ) {x y : Space n}
    (hxy : y ≠ x) (hsmall : ‖y - x‖ < 1)
    (hm : ∀ a b : Space n,
      f b - f a - poissonPenalty A ‖b - a‖ - ε * (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤
      f y - f x - poissonPenalty A ‖y - x‖ - ε * (‖x‖ ^ 2 + ‖y‖ ^ 2)) :
    Laplacian.laplacian f y - Laplacian.laplacian f x ≤ -8 * A + 4 * n * ε := by
  let r := ‖y - x‖
  have hr : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let e : Space n := r⁻¹ • (y - x)
  have he : ‖e‖ = 1 := by simp [e, norm_smul, r, hr.ne']
  have her : r • e = y - x := by dsimp [e]; rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  let J := reflect e
  let a : Space n := (-2 : ℝ) • e
  let g : Space n → ℝ := fun z => r + inner ℝ a z
  have hg : ContDiff ℝ 2 g := contDiff_const.add (innerSL ℝ a).contDiff
  have hg0 : g 0 = r := by simp [g]
  have hdistance : ∀ z : Space n, y + J z - (x + z) = g z • e := by
    intro z
    have hai : inner ℝ a z = (-2 : ℝ) * inner ℝ e z := by
      dsimp only [a]
      rw [real_inner_smul_left]
    change y + reflect e z - (x + z) = (r + inner ℝ a z) • e
    rw [reflect_apply he, hai, add_smul, her, neg_mul, neg_smul]
    abel
  have hnear : ∀ᶠ z in 𝓝 (0 : Space n), 0 < g z ∧ g z < 1 :=
    ((hg.continuous.isOpen_preimage _ isOpen_Ioo).mem_nhds (by simpa [hg0] using And.intro hr hsmall))
  let F : Space n → ℝ := fun z => f (y + J z) - f (x + z) -
    A * (2 * g z - (g z) ^ 2) - ε * (‖x + z‖ ^ 2 + ‖y + J z‖ ^ 2)
  have hfy : ContDiff ℝ 2 (fun z => f (y + J z)) :=
    hf.comp (contDiff_const.add J.contDiff)
  have hfx : ContDiff ℝ 2 (fun z => f (x + z)) := hf.comp (contDiff_const.add contDiff_id)
  have hnx : ContDiff ℝ 2 (fun z : Space n => ‖x + z‖ ^ 2) :=
    (contDiff_const.add contDiff_id).norm_sq ℝ
  have hny : ContDiff ℝ 2 (fun z : Space n => ‖y + J z‖ ^ 2) :=
    (contDiff_const.add J.contDiff).norm_sq ℝ
  have hp : ContDiff ℝ 2 (fun z => A * (2 * g z - (g z) ^ 2)) := by fun_prop
  have hq : ContDiff ℝ 2 (fun z => ε * (‖x + z‖ ^ 2 + ‖y + J z‖ ^ 2)) := by fun_prop
  have hF : ContDiff ℝ 2 F := ((hfy.sub hfx).sub hp).sub hq
  have hmax : IsLocalMax F 0 := by
    filter_upwards [hnear] with z hz
    have hnorm : ‖y + J z - (x + z)‖ = g z := by
      rw [hdistance, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos hz.1]
    have hh := hm (x + z) (y + J z)
    rw [hnorm, poissonPenalty_of_le A hz.2.le, poissonPenalty_of_le A hsmall.le] at hh
    simpa [F, hg0, r] using hh
  have hl := laplacian_nonpos_of_local_max hF hmax
  have hly : Laplacian.laplacian (fun z => f (y + J z)) 0 = Laplacian.laplacian f y := by
    have ht : ContDiff ℝ 2 (fun u => f (y + u)) := hf.comp (contDiff_const.add contDiff_id)
    simpa only [map_zero, laplacian_translate hf, add_zero] using laplacian_comp_isometry ht J 0
  have hns : ContDiff ℝ 2 (fun z : Space n => ‖z‖ ^ 2) := contDiff_id.norm_sq ℝ
  have hlny : Laplacian.laplacian (fun z => ‖y + J z‖ ^ 2) 0 = 2 * n := by
    have ht : ContDiff ℝ 2 (fun u : Space n => ‖y + u‖ ^ 2) :=
      (contDiff_const.add contDiff_id).norm_sq ℝ
    simpa only [map_zero, laplacian_translate hns, laplacian_norm_sq] using
      laplacian_comp_isometry ht J 0
  have hal : ‖a‖ ^ 2 = 4 := by simp [a, norm_smul, he]; norm_num
  have hlg : Laplacian.laplacian g 0 = 0 := laplacian_affine a r 0
  have hlgs : Laplacian.laplacian (fun z => g z ^ 2) 0 = 8 := by
    rw [show (fun z => g z ^ 2) = (fun z => (r + inner ℝ a z) ^ 2) from rfl,
      laplacian_affine_sq, hal]
    norm_num
  have hg2 : ContDiff ℝ 2 (fun z => 2 * g z) := contDiff_const.mul hg
  dsimp only [F] at hl
  rw [laplacian_fun_sub ((hfy.sub hfx).sub hp) hq,
    laplacian_fun_sub (hfy.sub hfx) hp, laplacian_fun_sub hfy hfx,
    hly, laplacian_translate hf,
    laplacian_fun_const_mul (hg2.sub (hg.pow 2)),
    laplacian_fun_sub hg2 (hg.pow 2),
    laplacian_fun_const_mul hg, hlg, hlgs,
    laplacian_fun_const_mul (hnx.add hny), laplacian_fun_add hnx hny,
    laplacian_translate hns, laplacian_norm_sq, hlny] at hl
  simp only [add_zero] at hl
  linarith

lemma bounded_poisson_lipschitz {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) {M C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hbound : ∀ x, |f x| ≤ M) (hlap : ∀ x, |Laplacian.laplacian f x| ≤ C) :
    ∀ x y, |f y - f x| ≤ 2 * (2 * M + C + 1) * ‖y - x‖ := by
  let A := 2 * M + C + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hlarge : 2 * M < A := by dsimp [A]; linarith
  have honeway : ∀ x y, f y - f x ≤ 2 * A * ‖y - x‖ := by
    intro x₀ y₀
    by_contra hbad
    have hbad' : 2 * A * ‖y₀ - x₀‖ < f y₀ - f x₀ := lt_of_not_ge hbad
    let δ := f y₀ - f x₀ - poissonPenalty A ‖y₀ - x₀‖
    have hδ : 0 < δ := by
      dsimp [δ]
      have hh := poissonPenalty_le_linear hA.le (norm_nonneg (y₀ - x₀))
      linarith
    let S := ‖x₀‖ ^ 2 + ‖y₀‖ ^ 2
    have hS : 0 ≤ S := by dsimp [S]; positivity
    let ε := min (δ / (2 * (S + 1))) (1 / (n + 1 : ℝ))
    have hε : 0 < ε := lt_min (by positivity) (by positivity)
    have hεS : ε * (S + 1) ≤ δ / 2 := by
      have hh := min_le_left (δ / (2 * (S + 1))) (1 / (n + 1 : ℝ))
      have hh' := (le_div_iff₀ (show 0 < 2 * (S + 1) by positivity)).mp hh
      change ε * (2 * (S + 1)) ≤ δ at hh'
      linarith
    have hεn : (n : ℝ) * ε ≤ 1 := by
      have hh := min_le_right (δ / (2 * (S + 1))) (1 / (n + 1 : ℝ))
      have hh' := (le_div_iff₀ (show 0 < (n : ℝ) + 1 by positivity)).mp hh
      change ε * ((n : ℝ) + 1) ≤ 1 at hh'
      nlinarith
    have hpos₀ : 0 < f y₀ - f x₀ - poissonPenalty A ‖y₀ - x₀‖ -
        ε * (‖x₀‖ ^ 2 + ‖y₀‖ ^ 2) := by
      change 0 < δ - ε * S
      nlinarith
    obtain ⟨x, y, hm⟩ := poisson_maximum hf.continuous hM hbound hA.le hε
    have hp : 0 < f y - f x - poissonPenalty A ‖y - x‖ - ε * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
      hpos₀.trans_le (hm x₀ y₀)
    have hpen : 0 ≤ ε * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by positivity
    have hxy : y ≠ x := by
      rintro rfl
      simp only [sub_self, norm_zero, poissonPenalty, sub_zero, max_eq_left zero_le_one,
        one_pow, sub_self, mul_zero] at hp
      linarith
    have hs : ‖y - x‖ < 1 := by
      by_contra h
      rw [poissonPenalty_of_ge A (le_of_not_gt h)] at hp
      have hb₁ := (abs_le.mp (hbound x)).1
      have hb₂ := (abs_le.mp (hbound y)).2
      linarith
    have hl := laplacian_poisson_at_max hf A ε hxy hs hm
    have hb₁ := (abs_le.mp (hlap y)).1
    have hb₂ := (abs_le.mp (hlap x)).2
    dsimp [A] at hl
    linarith
  intro x y
  apply abs_le.mpr
  constructor
  · have h := honeway y x
    rw [norm_sub_rev x y] at h
    linarith
  · exact honeway x y

def difference {n : ℕ} (h : Space n) (f : Space n → ℝ) : Space n → ℝ :=
  fun x => f (x + h) - f x

def iterDifference {n : ℕ} : List (Space n) → (Space n → ℝ) → Space n → ℝ
  | [], f => f
  | h :: l, f => difference h (iterDifference l f)

def differenceScale {n : ℕ} (l : List (Space n)) : ℝ := (l.map (fun h => ‖h‖)).prod

def DifferenceBound {n : ℕ} (k : ℕ) (f : Space n → ℝ) (M : ℝ) : Prop :=
  ∀ l : List (Space n), l.length ≤ k → ∀ x, |iterDifference l f x| ≤ M * differenceScale l

lemma differenceScale_nonneg {n : ℕ} (l : List (Space n)) : 0 ≤ differenceScale l := by
  apply List.prod_nonneg
  intro a ha
  obtain ⟨h, _, rfl⟩ := List.mem_map.mp ha
  exact norm_nonneg h

lemma difference_comm {n : ℕ} (h k : Space n) (f : Space n → ℝ) :
    difference h (difference k f) = difference k (difference h f) := by
  funext x
  simp only [difference]
  rw [show x + h + k = x + k + h by abel]
  ring

lemma iterDifference_difference {n : ℕ} (l : List (Space n)) (h : Space n) (f : Space n → ℝ) :
    iterDifference l (difference h f) = difference h (iterDifference l f) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [iterDifference, ih, difference_comm a h]

lemma iterDifference_add {n : ℕ} (l : List (Space n)) (f g : Space n → ℝ) :
    iterDifference l (fun x => f x + g x) = fun x => iterDifference l f x + iterDifference l g x := by
  induction l with
  | nil => rfl
  | cons h l ih =>
    funext x
    simp only [iterDifference, ih, difference]
    ring

lemma iterDifference_sub {n : ℕ} (l : List (Space n)) (f g : Space n → ℝ) :
    iterDifference l (fun x => f x - g x) = fun x => iterDifference l f x - iterDifference l g x := by
  induction l with
  | nil => rfl
  | cons h l ih =>
    funext x
    simp only [iterDifference, ih, difference]
    ring

lemma iterDifference_const_mul {n : ℕ} (l : List (Space n)) (c : ℝ) (f : Space n → ℝ) :
    iterDifference l (fun x => c * f x) = fun x => c * iterDifference l f x := by
  induction l with
  | nil => rfl
  | cons h l ih =>
    funext x
    simp only [iterDifference, ih, difference]
    ring

lemma iterDifference_translate {n : ℕ} (l : List (Space n)) (h : Space n) (f : Space n → ℝ) :
    iterDifference l (fun x => f (x + h)) = fun x => iterDifference l f (x + h) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    funext x
    simp only [iterDifference, ih, difference]
    rw [show x + a + h = x + h + a by abel]

lemma DifferenceBound.mono {n k j : ℕ} {f : Space n → ℝ} {M : ℝ}
    (hf : DifferenceBound k f M) (hj : j ≤ k) : DifferenceBound j f M :=
  fun l hl => hf l (hl.trans hj)

lemma DifferenceBound.translate {n k : ℕ} {f : Space n → ℝ} {M : ℝ}
    (hf : DifferenceBound k f M) (h : Space n) : DifferenceBound k (fun x => f (x + h)) M := by
  intro l hl x
  rw [iterDifference_translate]
  exact hf l hl (x + h)

lemma DifferenceBound.normalized_difference {n k : ℕ} {f : Space n → ℝ} {M : ℝ}
    (hf : DifferenceBound (k + 1) f M) {h : Space n} (hh : h ≠ 0) :
    DifferenceBound k (fun x => ‖h‖⁻¹ * difference h f x) M := by
  intro l hl x
  rw [iterDifference_const_mul, iterDifference_difference, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg h))]
  have hb := hf (h :: l) (by simpa using Nat.add_le_add_right hl 1) x
  change |difference h (iterDifference l f) x| ≤ M * (‖h‖ * differenceScale l) at hb
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hz := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hn.le)
  calc
    ‖h‖⁻¹ * |difference h (iterDifference l f) x| ≤ ‖h‖⁻¹ * (M * (‖h‖ * differenceScale l)) := hz
    _ = M * differenceScale l := by field_simp

lemma DifferenceBound.sub {n k : ℕ} {f g : Space n → ℝ} {M N : ℝ}
    (hf : DifferenceBound k f M) (hg : DifferenceBound k g N) :
    DifferenceBound k (fun x => f x - g x) (M + N) := by
  intro l hl x
  rw [iterDifference_sub]
  calc
    |iterDifference l f x - iterDifference l g x| ≤ |iterDifference l f x| + |iterDifference l g x| := abs_sub _ _
    _ ≤ M * differenceScale l + N * differenceScale l := add_le_add (hf l hl x) (hg l hl x)
    _ = (M + N) * differenceScale l := by ring

lemma DifferenceBound.mul {n k : ℕ} {f g : Space n → ℝ} {M N : ℝ}
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hf : DifferenceBound k f M) (hg : DifferenceBound k g N) :
    DifferenceBound k (fun x => f x * g x) ((2 : ℝ) ^ k * M * N) := by
  induction k generalizing f g with
  | zero =>
    intro l hl x
    have he : l = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hl)
    subst l
    have hfb := hf [] (by simp) x
    have hgb := hg [] (by simp) x
    simpa [iterDifference, differenceScale, abs_mul] using
      mul_le_mul hfb hgb (abs_nonneg _) (by simpa [differenceScale] using hM)
  | succ k ih =>
    intro l hl x
    cases l with
    | nil =>
      have hb := mul_le_mul (hf [] (by simp) x) (hg [] (by simp) x) (abs_nonneg _)
        (show 0 ≤ M * differenceScale ([] : List (Space n)) by simpa [differenceScale] using hM)
      have hp : 1 ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
      simp only [iterDifference, differenceScale, List.map_nil, List.prod_nil, mul_one, abs_mul] at hb ⊢
      calc
        |f x| * |g x| ≤ M * N := hb
        _ ≤ 2 ^ (k + 1) * M * N := by nlinarith [mul_nonneg hM hN]
    | cons h l =>
      by_cases hh : h = 0
      · subst h
        simp [iterDifference, difference, differenceScale]
      have hl' : l.length ≤ k := Nat.le_of_succ_le_succ hl
      let F : Space n → ℝ := fun x => ‖h‖⁻¹ * difference h f x
      let G : Space n → ℝ := fun x => ‖h‖⁻¹ * difference h g x
      have hF : DifferenceBound k F M := hf.normalized_difference hh
      have hG : DifferenceBound k G N := hg.normalized_difference hh
      have hf' : DifferenceBound k f M := hf.mono (Nat.le_succ k)
      have hg' : DifferenceBound k (fun x => g (x + h)) N :=
        (hg.mono (Nat.le_succ k)).translate h
      have ht₁ := ih hF hg' l hl' x
      have ht₂ := ih hf' hG l hl' x
      have he : difference h (fun x => f x * g x) =
          fun x => ‖h‖ * (F x * g (x + h) + f x * G x) := by
        funext x
        dsimp [difference, F, G]
        field_simp
        ring
      have ht : iterDifference (h :: l) (fun x => f x * g x) x =
          ‖h‖ * (iterDifference l (fun x => F x * g (x + h)) x +
            iterDifference l (fun x => f x * G x) x) := by
        change difference h (iterDifference l (fun x => f x * g x)) x = _
        rw [← iterDifference_difference, he, iterDifference_const_mul, iterDifference_add]
      rw [ht, abs_mul, abs_of_nonneg (norm_nonneg h)]
      have hab := (abs_add_le _ _).trans (add_le_add ht₁ ht₂)
      have hmult := mul_le_mul_of_nonneg_left hab (norm_nonneg h)
      calc
        _ ≤ ‖h‖ * (2 ^ k * M * N * differenceScale l + 2 ^ k * M * N * differenceScale l) := hmult
        _ = 2 ^ (k + 1) * M * N * differenceScale (h :: l) := by
          simp only [differenceScale, List.map_cons, List.prod_cons, pow_succ]
          ring

lemma iterDifference_contDiff {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (l : List (Space n)) : ContDiff ℝ 2 (iterDifference l f) := by
  induction l with
  | nil => exact hf
  | cons h l ih => exact (ih.comp (contDiff_id.add contDiff_const)).sub ih

lemma laplacian_difference {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    (h x : Space n) : Laplacian.laplacian (difference h f) x = difference h (Laplacian.laplacian f) x := by
  have hc : ContDiff ℝ 2 (fun x => f (x + h)) := hf.comp (contDiff_id.add contDiff_const)
  rw [show difference h f = (fun x => f (x + h)) - f by rfl,
    hc.contDiffAt.laplacian_sub hf.contDiffAt]
  change Laplacian.laplacian (fun z => f (z + h)) x - Laplacian.laplacian f x = _
  rw [show (fun z => f (z + h)) = (fun z => f (h + z)) by funext z; rw [add_comm],
    laplacian_translate hf]
  simp [difference, add_comm]

lemma laplacian_iterDifference {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    (l : List (Space n)) : Laplacian.laplacian (iterDifference l f) = iterDifference l (Laplacian.laplacian f) := by
  induction l with
  | nil => rfl
  | cons h l ih =>
    funext x
    rw [iterDifference, laplacian_difference (iterDifference_contDiff hf l), ih]
    rfl

lemma iterDifference_eq_zero_of_scale_eq_zero {n : ℕ} (l : List (Space n))
    (hl : differenceScale l = 0) (f : Space n → ℝ) : iterDifference l f = 0 := by
  induction l with
  | nil => simp [differenceScale] at hl
  | cons h l ih =>
    have hp : ‖h‖ * differenceScale l = 0 := hl
    rcases mul_eq_zero.mp hp with hh | hl
    · have hz : h = 0 := norm_eq_zero.mp hh
      subst h
      ext x
      simp [iterDifference, difference]
    · rw [iterDifference, ih hl]
      ext x
      simp [difference]

end RegularitySupport.DeGiorgi
end

end OAI
