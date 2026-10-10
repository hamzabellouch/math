import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Interpolation.PrimitiveDirections
import OAI.AlgebraicGeometry.Seshadri.Interpolation.LaurentMoments

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
def latticeHeight (i j : ℤ) (p : ℤ × ℤ) : ℤ := i * p.2 - j * p.1

def latticeCoord (r : ℕ) (i j a b : ℤ) (e p : ℤ × ℤ) : ℤ × ℤ :=
  (a * (p.1 - e.1) + b * (p.2 - e.2),
    (latticeHeight i j p - latticeHeight i j e) / (r : ℤ))

theorem latticeCoord_reconstruct (r : ℕ) (i j a b : ℤ) (e p : ℤ × ℤ)
    (hbez : a * i + b * j = 1)
    (hp : (r : ℤ) ∣ latticeHeight i j p - latticeHeight i j e) :
    (i * (latticeCoord r i j a b e p).1 - r * b * (latticeCoord r i j a b e p).2,
      j * (latticeCoord r i j a b e p).1 + r * a * (latticeCoord r i j a b e p).2) =
      (p.1 - e.1, p.2 - e.2) := by
  have hd := Int.mul_ediv_cancel' hp
  dsimp [latticeHeight] at hd
  apply Prod.ext
  · dsimp [latticeCoord, latticeHeight]
    linear_combination (p.1 - e.1) * hbez - b * hd
  · dsimp [latticeCoord, latticeHeight]
    linear_combination (p.2 - e.2) * hbez + a * hd

theorem latticeCoord_injOn (r : ℕ) (i j a b : ℤ) (e : ℤ × ℤ)
    (hbez : a * i + b * j = 1) :
    Set.InjOn (latticeCoord r i j a b e)
      {p | (r : ℤ) ∣ latticeHeight i j p - latticeHeight i j e} := by
  intro p hp q hq he
  have hp' := latticeCoord_reconstruct r i j a b e p hbez hp
  have hq' := latticeCoord_reconstruct r i j a b e q hbez hq
  rw [he] at hp'
  have hdiff := hp'.symm.trans hq'
  exact Prod.ext (by linarith only [congrArg Prod.fst hdiff])
    (by linarith only [congrArg Prod.snd hdiff])

noncomputable def cyclicTorusPoint (ζ : ℂ) (i j : ℤ) (l : ℕ) : ℂ × ℂ :=
  (ζ ^ (-((l : ℤ) * j)), ζ ^ ((l : ℤ) * i))

theorem cyclicTorusPoint_character (ζ : ℂ) (hζ : ζ ≠ 0) (i j : ℤ) (l : ℕ)
    (p : ℤ × ℤ) :
    (cyclicTorusPoint ζ i j l).1 ^ p.1 * (cyclicTorusPoint ζ i j l).2 ^ p.2 =
      ζ ^ ((l : ℤ) * latticeHeight i j p) := by
  dsimp [cyclicTorusPoint, latticeHeight]
  rw [← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ]
  congr 1
  ring

theorem cyclicTorusPoint_injective (ζ : ℂ) (r : ℕ) (hr : 0 < r)
    (hζ : IsPrimitiveRoot ζ r) (i j : ℤ) (hprim : IsCoprime i j) :
    Function.Injective (fun l : Fin r => cyclicTorusPoint ζ i j l) := by
  obtain ⟨a, b, hab⟩ := hprim
  intro l n he
  have hχ := congrArg (fun p : ℂ × ℂ => p.1 ^ (-b) * p.2 ^ a) he
  have hζ0 := (hζ.isUnit hr.ne').ne_zero
  simp only [cyclicTorusPoint_character ζ hζ0 i j _ (-b, a)] at hχ
  have hh : latticeHeight i j (-b, a) = 1 := by dsimp [latticeHeight]; nlinarith only [hab]
  rw [hh] at hχ
  simp only [mul_one, zpow_natCast] at hχ
  exact Fin.ext (hζ.pow_inj l.isLt n.isLt hχ)

noncomputable def latticeAffine (r : ℕ) (i j a b : ℤ) (e : ℤ × ℤ) :
    (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) where
  toFun p := ((a : ℝ) * (p.1 - e.1) + (b : ℝ) * (p.2 - e.2),
    ((i : ℝ) * (p.2 - e.2) - (j : ℝ) * (p.1 - e.1)) / r)
  linear :=
    { toFun := fun p => ((a : ℝ) * p.1 + (b : ℝ) * p.2,
        ((i : ℝ) * p.2 - (j : ℝ) * p.1) / r)
      map_add' := by intro p q; ext <;> dsimp <;> ring
      map_smul' := by intro c p; ext <;> dsimp <;> ring }
  map_vadd' := by intro p v; ext <;> dsimp <;> ring

theorem latticeCoord_cast (r : ℕ) (hr : 0 < r) (i j a b : ℤ) (e p : ℤ × ℤ)
    (hp : (r : ℤ) ∣ latticeHeight i j p - latticeHeight i j e) :
    (((latticeCoord r i j a b e p).1 : ℝ), ((latticeCoord r i j a b e p).2 : ℝ)) =
      latticeAffine r i j a b e ((p.1 : ℝ), (p.2 : ℝ)) := by
  have hrR : ((r : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  apply Prod.ext
  · simp [latticeCoord, latticeAffine]
  · dsimp [latticeCoord, latticeAffine]
    rw [Int.cast_div hp hrR]
    push_cast
    simp only [latticeHeight]
    push_cast
    ring

theorem latticeAffine_det (r : ℕ) (i j a b : ℤ) (e : ℤ × ℤ)
    (hbez : a * i + b * j = 1) (p q v : ℝ × ℝ) :
    ((latticeAffine r i j a b e q).1 - (latticeAffine r i j a b e p).1) *
        ((latticeAffine r i j a b e v).2 - (latticeAffine r i j a b e p).2) -
      ((latticeAffine r i j a b e v).1 - (latticeAffine r i j a b e p).1) *
        ((latticeAffine r i j a b e q).2 - (latticeAffine r i j a b e p).2) =
      ((q.1 - p.1) * (v.2 - p.2) - (v.1 - p.1) * (q.2 - p.2)) / r := by
  have hbR : (a : ℝ) * i + (b : ℝ) * j = 1 := by exact_mod_cast hbez
  dsimp [latticeAffine]
  linear_combination (((q.1 - p.1) * (v.2 - p.2) - (v.1 - p.1) *
    (q.2 - p.2)) / r) * hbR

theorem MomentJetZero.congr {α : Type*} (s : Finset α)
    (c c' x x' y y' : α → ℂ) (m : ℕ) (hjet : MomentJetZero s c x y m)
    (hc : ∀ p ∈ s, c' p = c p) (hx : ∀ p ∈ s, x' p = x p)
    (hy : ∀ p ∈ s, y' p = y p) : MomentJetZero s c' x' y' m := by
  intro a b hab
  convert hjet a b hab using 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [hc p hp, hx p hp, hy p hp]

theorem MomentJetZero.nonzeroSupport {α : Type*} (s : Finset α)
    (c x y : α → ℂ) (m : ℕ) (hjet : MomentJetZero s c x y m) :
    MomentJetZero (s.filter (fun p => c p ≠ 0)) c x y m := by
  classical
  intro a b hab
  rw [Finset.sum_filter]
  convert hjet a b hab using 1
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : c p = 0 <;> simp [hp]

theorem latticeCoord_cast_complex (r : ℕ) (hr : 0 < r) (i j a b : ℤ) (e p : ℤ × ℤ)
    (hp : (r : ℤ) ∣ latticeHeight i j p - latticeHeight i j e) :
    (((latticeCoord r i j a b e p).1 : ℂ), ((latticeCoord r i j a b e p).2 : ℂ)) =
      ((a : ℂ) * p.1 + (b : ℂ) * p.2 - ((a : ℂ) * e.1 + (b : ℂ) * e.2),
        (-(j : ℂ) / r) * p.1 + ((i : ℂ) / r) * p.2 +
          (((j : ℂ) * e.1 - (i : ℂ) * e.2) / r)) := by
  have hrC : ((r : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  apply Prod.ext
  · simp only [latticeCoord, Int.cast_add, Int.cast_mul, Int.cast_sub]
    ring
  · dsimp only [latticeCoord]
    rw [Int.cast_div hp hrC]
    simp only [latticeHeight]
    push_cast
    ring

theorem lattice_coordinate_moments (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (r m : ℕ)
    (hr : 0 < r) (i j a b : ℤ) (e : ℤ × ℤ)
    (hcos : ∀ p ∈ s, (r : ℤ) ∣ latticeHeight i j p - latticeHeight i j e)
    (hjet : MomentJetZero s c (fun p => (p.1 : ℂ)) (fun p => (p.2 : ℂ)) m) :
    MomentJetZero s c (fun p => ((latticeCoord r i j a b e p).1 : ℂ))
      (fun p => ((latticeCoord r i j a b e p).2 : ℂ)) m := by
  have h := MomentJetZero.affine s c (fun p => (p.1 : ℂ)) (fun p => (p.2 : ℂ)) m hjet
    (a : ℂ) (b : ℂ) (-((a : ℂ) * e.1 + (b : ℂ) * e.2))
    (-(j : ℂ) / r) ((i : ℂ) / r)
    (((j : ℂ) * e.1 - (i : ℂ) * e.2) / r)
  intro x y hxy
  convert h x y hxy using 1
  apply Finset.sum_congr rfl
  intro p hp
  have heq := latticeCoord_cast_complex r hr i j a b e p (hcos p hp)
  have h1 := congrArg Prod.fst heq
  have h2 := congrArg Prod.snd heq
  dsimp only at h1 h2
  dsimp only
  rw [h1, h2]
  simp only [sub_eq_add_neg]

theorem lattice_moments (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (r m : ℕ)
    (hr : 0 < r) (i j a b : ℤ) (e : ℤ × ℤ) (hbez : a * i + b * j = 1)
    (hcos : ∀ p ∈ s, (r : ℤ) ∣ latticeHeight i j p - latticeHeight i j e)
    (hjet : MomentJetZero s c (fun p => (p.1 : ℂ)) (fun p => (p.2 : ℂ)) m) :
    EulerJetZero (s.image (latticeCoord r i j a b e))
      (c ∘ Function.invFunOn (latticeCoord r i j a b e) s) m := by
  have hinj : Set.InjOn (latticeCoord r i j a b e) s :=
    (latticeCoord_injOn r i j a b e hbez).mono hcos
  have h' := lattice_coordinate_moments s c r m hr i j a b e hcos hjet
  exact (eulerJetZero_iff_momentJetZero _ _ _).mpr
    (MomentJetZero.image s c (latticeCoord r i j a b e) hinj
      (fun p => (p.1 : ℂ)) (fun p => (p.2 : ℂ)) m h')

theorem latticeAffine_snd_sub (r : ℕ) (i j a b : ℤ) (e : ℤ × ℤ)
    (p q : ℝ × ℝ) :
    (latticeAffine r i j a b e q).2 - (latticeAffine r i j a b e p).2 =
      (directionProjection i j q - directionProjection i j p) / r := by
  dsimp [latticeAffine, directionProjection]
  ring

theorem sqrt_mul_div (r : ℕ) (hr : 0 < r) (H : ℝ) (hH : 0 < H) :
    Real.sqrt ((r : ℝ) * H) / r = Real.sqrt (H / r) := by
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  rw [Real.sqrt_div (le_of_lt hH), Real.sqrt_mul hrR.le]
  have hs : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hrR
  have hs2 := Real.sq_sqrt hrR.le
  apply (div_eq_div_iff hrR.ne' hs.ne').mpr
  calc
    _ = Real.sqrt H * (Real.sqrt (r : ℝ)) ^ 2 := by ring
    _ = _ := by rw [hs2]


end MaximalSeshadri.Interpolation
end

end OAI
