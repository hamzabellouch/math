import Mathlib
import OAI.GroupTheory.SimpleAmenable.Arithmetic.PolygonArithmetic

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section LatticeCounting

def embeddingBox (x y a b : ℝ) : Set CutRing :=
  {z | ordinary z ∈ Set.Icc x (x + a) ∧ conjugate z ∈ Set.Icc y (y + b)}

theorem embeddingBox_floor_injective (x y a b : ℝ) (hb : 0 < b) :
    Set.InjOn (fun z : CutRing => ⌊b * ordinary z⌋) (embeddingBox x y a b) := by
  intro z hz w hw he
  dsimp only at he
  by_contra hn
  have hnorm := one_le_abs_cut_norm (sub_ne_zero.mpr hn)
  rw [map_sub, map_sub, abs_mul] at hnorm
  have ho : |b * (ordinary z - ordinary w)| < 1 := by
    have hz₁ := Int.floor_le (b * ordinary z)
    have hz₂ := Int.lt_floor_add_one (b * ordinary z)
    have hw₁ := Int.floor_le (b * ordinary w)
    have hw₂ := Int.lt_floor_add_one (b * ordinary w)
    rw [he] at hz₁ hz₂
    apply abs_lt.mpr
    constructor <;> nlinarith
  have hc : |conjugate z - conjugate w| ≤ b := by
    exact abs_le.mpr ⟨by linarith [hz.2.1, hw.2.2], by linarith [hz.2.2, hw.2.1]⟩
  rw [abs_mul, abs_of_pos hb] at ho
  have hprod := mul_le_mul_of_nonneg_left hc (abs_nonneg (ordinary z - ordinary w))
  nlinarith

theorem embeddingBox_floor_mapsTo (x y a b : ℝ) (hb : 0 ≤ b) :
    Set.MapsTo (fun z : CutRing => ⌊b * ordinary z⌋) (embeddingBox x y a b)
      (Set.Icc ⌊b * x⌋ ⌊b * (x + a)⌋) := by
  intro z hz
  exact ⟨Int.floor_mono (mul_le_mul_of_nonneg_left hz.1.1 hb),
    Int.floor_mono (mul_le_mul_of_nonneg_left hz.1.2 hb)⟩

theorem embeddingBox_finite (x y a b : ℝ) (hb : 0 < b) :
    (embeddingBox x y a b).Finite :=
  (Set.finite_Icc _ _).of_injOn (embeddingBox_floor_mapsTo x y a b hb.le)
    (embeddingBox_floor_injective x y a b hb)

theorem embeddingBox_card_le (x y a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b)
    (s : Finset CutRing) (hs : (s : Set CutRing) ⊆ embeddingBox x y a b) :
    (s.card : ℝ) ≤ a * b + 2 := by
  classical
  have hinj := (embeddingBox_floor_injective x y a b hb).mono hs
  have hcard : s.card ≤ (Finset.Icc ⌊b * x⌋ ⌊b * (x + a)⌋).card := by
    calc
      _ = (s.image (fun z => ⌊b * ordinary z⌋)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ _ := Finset.card_le_card (by
        intro k hk
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hk
        exact Finset.mem_Icc.mpr (embeddingBox_floor_mapsTo x y a b hb.le (hs hz)))
  have hle : ⌊b * x⌋ ≤ ⌊b * (x + a)⌋ + 1 := by
    have := Int.floor_mono (show b * x ≤ b * (x + a) by nlinarith)
    omega
  have he := Int.card_Icc_of_le ⌊b * x⌋ ⌊b * (x + a)⌋ hle
  have he' : ((Finset.Icc ⌊b * x⌋ ⌊b * (x + a)⌋).card : ℝ) =
      (⌊b * (x + a)⌋ : ℝ) + 1 - (⌊b * x⌋ : ℝ) := by exact_mod_cast he
  have hc : (s.card : ℝ) ≤ ((Finset.Icc ⌊b * x⌋ ⌊b * (x + a)⌋).card : ℝ) := by
    exact_mod_cast hcard
  rw [he'] at hc
  linarith [Int.floor_le (b * (x + a)), Int.lt_floor_add_one (b * x)]

def dividedEmbeddingBox (d x y a b : ℝ) : Set CutRing :=
  {z | ordinary z / d ∈ Set.Icc x (x + a) ∧
    conjugate z / d ∈ Set.Icc y (y + b)}

theorem dividedEmbeddingBox_eq (d x y a b : ℝ) (hd : 0 < d) :
    dividedEmbeddingBox d x y a b = embeddingBox (d*x) (d*y) (d*a) (d*b) := by
  ext z
  simp only [dividedEmbeddingBox, embeddingBox, Set.mem_ofPred_eq, Set.mem_Icc,
    le_div_iff₀ hd, div_le_iff₀ hd]
  constructor <;> rintro ⟨⟨h₁,h₂⟩,⟨h₃,h₄⟩⟩ <;>
    constructor <;> constructor <;> nlinarith

theorem dividedEmbeddingBox_finite (d x y a b : ℝ) (hd : 0 < d) (hb : 0 < b) :
    (dividedEmbeddingBox d x y a b).Finite := by
  rw [dividedEmbeddingBox_eq d x y a b hd]
  exact embeddingBox_finite _ _ _ _ (mul_pos hd hb)

theorem dividedEmbeddingBox_card_le (d x y a b : ℝ)
    (hd : 0 < d) (ha : 0 ≤ a) (hb : 0 < b)
    (s : Finset CutRing) (hs : (s : Set CutRing) ⊆ dividedEmbeddingBox d x y a b) :
    (s.card : ℝ) ≤ d^2 * a * b + 2 := by
  rw [dividedEmbeddingBox_eq d x y a b hd] at hs
  convert embeddingBox_card_le _ _ _ _ (mul_nonneg hd.le ha) (mul_pos hd hb) s hs using 1; ring

theorem pairedEmbeddingBox_card_le (d : ℝ) (hd : 0 < d)
    (x₁ y₁ a₁ b₁ x₂ y₂ a₂ b₂ : ℝ)
    (ha₁ : 0 ≤ a₁) (hb₁ : 0 < b₁) (ha₂ : 0 ≤ a₂) (hb₂ : 0 < b₂)
    (s : Finset (CutRing × CutRing))
    (hs : ∀ z ∈ s, z.1 ∈ dividedEmbeddingBox d x₁ y₁ a₁ b₁ ∧
      z.2 ∈ dividedEmbeddingBox d x₂ y₂ a₂ b₂) :
    (s.card : ℝ) ≤ (d^2*a₁*b₁ + 2) * (d^2*a₂*b₂ + 2) := by
  classical
  have hc₁ := dividedEmbeddingBox_card_le d x₁ y₁ a₁ b₁ hd ha₁ hb₁
    (s.image Prod.fst) (by
      rintro z hz
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      exact (hs p hp).1)
  have hc₂ := dividedEmbeddingBox_card_le d x₂ y₂ a₂ b₂ hd ha₂ hb₂
    (s.image Prod.snd) (by
      rintro z hz
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      exact (hs p hp).2)
  have hc : s.card ≤ (s.image Prod.fst).card * (s.image Prod.snd).card := by
    rw [← Finset.card_product]
    apply Finset.card_le_card
    intro z hz
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hz, Finset.mem_image_of_mem _ hz⟩
  calc
    (s.card : ℝ) ≤ (s.image Prod.fst).card * (s.image Prod.snd).card := by exact_mod_cast hc
    _ ≤ _ := mul_le_mul hc₁ hc₂ (by positivity) (by positivity)

end LatticeCounting

section QuantitativeArithmetic

lemma floor_error (x : ℝ) : |(⌊x⌋ : ℝ) - x| ≤ 1 := by
  rw [abs_of_nonpos (sub_nonpos.mpr (Int.floor_le x))]
  linarith [Int.lt_floor_add_one x]

theorem quadratic_lattice_cover (u : CutRing) (hu : u ≠ 0) (x y : ℝ) :
    ∃ z : CutRing, |ordinary z - x| ≤ 3 * |ordinary u| ∧
      |conjugate z - y| ≤ 2 * |conjugate u| := by
  have huo : ordinary u ≠ 0 := by simpa using ordinary_injective.ne hu
  have huc : conjugate u ≠ 0 := by simpa using conjugate_injective.ne hu
  have hd : Real.goldenRatio - Real.goldenConj ≠ 0 := by
    rw [Real.goldenRatio_sub_goldenConj]
    exact ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  let b := (x / ordinary u - y / conjugate u) /
    (Real.goldenRatio - Real.goldenConj)
  let a := x / ordinary u - b * Real.goldenRatio
  have hb : b * (Real.goldenRatio - Real.goldenConj) =
      x / ordinary u - y / conjugate u := div_mul_cancel₀ _ hd
  have ha₁ : a + b * Real.goldenRatio = x / ordinary u := by dsimp [a]; ring
  have ha₂ : a + b * Real.goldenConj = y / conjugate u := by dsimp [a]; nlinarith [hb]
  have hx : ordinary u * (a + b * Real.goldenRatio) = x := by
    rw [ha₁]; exact mul_div_cancel₀ _ huo
  have hy : conjugate u * (a + b * Real.goldenConj) = y := by
    rw [ha₂]; exact mul_div_cancel₀ _ huc
  let z : CutRing := u * ((⌊a⌋ : CutRing) + (⌊b⌋ : CutRing) * cutTau)
  have ho : ordinary z - x = ordinary u *
      (((⌊a⌋ : ℝ) - a) + ((⌊b⌋ : ℝ) - b) * Real.goldenRatio) := by
    dsimp [z]
    simp only [map_mul,map_add,map_intCast,ordinary_cutTau]
    rw [← hx]; ring
  have hc : conjugate z - y = conjugate u *
      (((⌊a⌋ : ℝ) - a) + ((⌊b⌋ : ℝ) - b) * Real.goldenConj) := by
    dsimp [z]
    simp only [map_mul,map_add,map_intCast,conjugate_cutTau]
    rw [← hy]; ring
  have hr : |Real.goldenRatio| ≤ 2 := by
    rw [abs_of_pos Real.goldenRatio_pos]
    exact Real.goldenRatio_lt_two.le
  have hb' : |Real.goldenConj| ≤ 1 := by
    rw [abs_of_neg Real.goldenConj_neg]
    linarith [Real.neg_one_lt_goldenConj]
  have bound (t : ℝ) (B : ℝ) (ht : |t| ≤ B) :
      |((⌊a⌋ : ℝ) - a) + ((⌊b⌋ : ℝ) - b)*t| ≤ 1+B := by
    calc
      _ ≤ |(⌊a⌋ : ℝ)-a| + |((⌊b⌋ : ℝ)-b)*t| := abs_add_le _ _
      _ = |(⌊a⌋ : ℝ)-a| + |(⌊b⌋ : ℝ)-b| *|t| := by rw [abs_mul]
      _ ≤ 1 + 1*B := by gcongr; exact floor_error a; exact floor_error b
      _ = _ := by ring
  refine ⟨z,?_,?_⟩
  · rw [ho,abs_mul]
    have := mul_le_mul_of_nonneg_left (bound _ _ hr) (abs_nonneg (ordinary u))
    nlinarith
  · rw [hc,abs_mul]
    have := mul_le_mul_of_nonneg_left (bound _ _ hb') (abs_nonneg (conjugate u))
    nlinarith

theorem scaled_quadratic_lattice_cover (L : ℝ) (hL : 1 ≤ L) (x y : ℝ) :
    ∃ z : CutRing, |ordinary z - x| ≤ 6 / L ∧
      |conjugate z - y| ≤ 2 * L := by
  obtain ⟨k,hk,hk'⟩ := exists_nat_pow_near hL Real.one_lt_goldenRatio
  let u : CutRing := (cutTau - 1)^k
  have hτ : 0 < Real.goldenRatio^k := pow_pos Real.goldenRatio_pos _
  have ho : ordinary u = (Real.goldenRatio^k)⁻¹ := by
    simp only [u,map_pow,map_sub,ordinary_cutTau,map_one]
    rw [← inv_pow]
    congr 1
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have hc : |conjugate u| = Real.goldenRatio^k := by
    simp only [u,map_pow,map_sub,conjugate_cutTau,map_one,abs_pow]
    congr 1
    rw [abs_of_neg (by linarith [Real.goldenConj_neg] : Real.goldenConj - 1 < 0)]
    linarith [Real.goldenRatio_add_goldenConj]
  have hu : u ≠ 0 := by
    intro h
    have he : ordinary u = 0 := by rw [h,map_zero]
    rw [ho] at he
    exact (inv_ne_zero hτ.ne') he
  obtain ⟨z,hz,hz'⟩ := quadratic_lattice_cover u hu x y
  refine ⟨z,hz.trans ?_,hz'.trans ?_⟩
  · rw [ho,abs_of_pos (inv_pos.mpr hτ)]
    have hL0 : 0 < L := by linarith
    have hnear : L < 2*Real.goldenRatio^k := by
      rw [pow_succ] at hk'
      nlinarith [Real.goldenRatio_lt_two]
    apply (le_div_iff₀ hL0).mpr
    have he : (Real.goldenRatio^k)⁻¹ * Real.goldenRatio^k = 1 := inv_mul_cancel₀ hτ.ne'
    nlinarith [mul_lt_mul_of_pos_left hnear (inv_pos.mpr hτ)]
  · rw [hc]
    linarith

theorem endpoint_separation {z : CutRing} (hz : z ≠ 0) {n : ℕ} (hn : 1 ≤ n)
    (ho : |ordinary z| ≤ 1) (hq : |(endpointLabel z : ℝ)| ≤ n) :
    1 / (4 * (n : ℝ)) ≤ |ordinary z| := by
  have hsqrt : Real.sqrt 5 ≤ 3 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have he : conjugate z = ordinary z - (endpointLabel z : ℝ)*Real.sqrt 5 := by
    have h := (eq_div_iff (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)))).mp
      (endpointLabel_embedding z)
    linarith
  have hc : |conjugate z| ≤ 4*(n:ℝ) := by
    rw [he]
    calc
      _ ≤ |ordinary z| + |(endpointLabel z:ℝ)*Real.sqrt 5| := by simpa using abs_sub_le (ordinary z) 0 ((endpointLabel z:ℝ)*Real.sqrt 5)
      _ = |ordinary z| + |(endpointLabel z:ℝ)| *Real.sqrt 5 := by
        rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg 5)]
      _ ≤ 1 + (n:ℝ)*3 := by gcongr
      _ ≤ _ := by linarith
  have hnorm := one_le_abs_cut_norm hz
  rw [abs_mul] at hnorm
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 4*(n:ℝ))).mpr
  nlinarith [mul_le_mul_of_nonneg_left hc (abs_nonneg (ordinary z))]

theorem coordinate_window_net (n : ℕ) (hn : 1 ≤ n) (q : ℤ) (t : ℝ) :
    ∃ z : CutRing, q ≤ endpointLabel z ∧ endpointLabel z < q + n ∧
      |ordinary z - t| ≤ 100 / (n : ℝ) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  by_cases hn32 : 32 ≤ n
  · have hn32' : (32:ℝ) ≤ n := by exact_mod_cast hn32
    let c : ℝ := (q:ℝ) + (n:ℝ)/2
    obtain ⟨z,ho,hb⟩ := scaled_quadratic_lattice_cover ((n:ℝ)/16) (by linarith)
      t (t-c*Real.sqrt 5)
    have ho' : |ordinary z-t| ≤ 96/(n:ℝ) := by
      convert ho using 1; field_simp; ring
    have hb' : |conjugate z-(t-c*Real.sqrt 5)| ≤ (n:ℝ)/8 := by
      convert hb using 1; ring
    have hs : 1 ≤ Real.sqrt 5 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5),Real.sqrt_nonneg 5]
    have hsmall : 96/(n:ℝ) ≤ (n:ℝ)/8 := by
      apply (div_le_iff₀ hn0).mpr
      nlinarith
    have hlabel : |(endpointLabel z:ℝ)-c| ≤ (n:ℝ)/4 := by
      have he : ((endpointLabel z:ℝ)-c)*Real.sqrt 5 =
          (ordinary z-t)-(conjugate z-(t-c*Real.sqrt 5)) := by
        have he := (eq_div_iff (ne_of_gt (lt_of_lt_of_le zero_lt_one hs))).mp
          (endpointLabel_embedding z)
        nlinarith [he]
      have htri : |(ordinary z-t)-(conjugate z-(t-c*Real.sqrt 5))| ≤
          |ordinary z-t| + |conjugate z-(t-c*Real.sqrt 5)| := by
        simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (ordinary z-t) 0 (conjugate z-(t-c*Real.sqrt 5))
      rw [← he,abs_mul,abs_of_nonneg (le_trans zero_le_one hs)] at htri
      nlinarith [abs_nonneg ((endpointLabel z:ℝ)-c)]
    have hlow : (q:ℝ) ≤ (endpointLabel z:ℝ) := by
      have hh := (abs_le.mp hlabel).1
      dsimp [c] at hh
      linarith
    have hhigh : (endpointLabel z:ℝ) < (q:ℝ)+(n:ℝ) := by
      have hh := (abs_le.mp hlabel).2
      dsimp [c] at hh
      linarith
    refine ⟨z,by exact_mod_cast hlow,by exact_mod_cast hhigh,ho'.trans ?_⟩
    apply div_le_div_of_nonneg_right (by norm_num) hn0.le
  · let z : CutRing := ⟨⌊t-(q:ℝ)*Real.goldenRatio⌋,q⟩
    refine ⟨z,le_rfl,by change q < q+(n:ℤ); omega,?_⟩
    have he : ordinary z-t = (⌊t-(q:ℝ)*Real.goldenRatio⌋:ℝ)-
        (t-(q:ℝ)*Real.goldenRatio) := by simp only [ordinary_apply,z]; ring
    rw [he]
    apply (floor_error _).trans
    apply (le_div_iff₀ hn0).mpr
    have : (n:ℝ) < 32 := by exact_mod_cast (lt_of_not_ge hn32)
    linarith

end QuantitativeArithmetic

end SimpleAmenable
end
end

end OAI
