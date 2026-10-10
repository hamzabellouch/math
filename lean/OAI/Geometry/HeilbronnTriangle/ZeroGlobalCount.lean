import OAI.Geometry.HeilbronnTriangle.ZeroCombinedShell
import OAI.Geometry.HeilbronnTriangle.ZeroNormalDyadic

namespace OAI


noncomputable section
namespace Problem355.ZeroGlobalCount

open Matrix PrimitiveNormal ZeroDeterminantCount
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def countConstant (Ca Cg Cd : ℝ) : ℝ :=
  4 * (1024 * Ca + 3 * (125 * Cg + 512 * Cd)) * planeConstant

lemma countConstant_nonneg {Ca Cg Cd : ℝ}
    (ha : 0 ≤ Ca) (hg : 0 ≤ Cg) (hd : 0 ≤ Cd) :
    0 ≤ countConstant Ca Cg Cd := by
  unfold countConstant planeConstant
  positivity

theorem weighted_count_le_log
    (D : RowData) (q N : ℕ) [Fact q.Prime]
    (hN : 1 ≤ N) (hEq : IsUnit (D.E : ZMod q))
    (hparam : D.h ^ 26 ≤ (q : ℝ))
    (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (W : Matrix (Fin 3) (Fin 3) ℤ → ℝ)
    (Ca Cg Cd : ℝ) (hCa : 0 ≤ Ca) (hCg : 0 ≤ Cg) (hCd : 0 ≤ Cd)
    (hW : ∀ A ∈ S, 0 ≤ W A)
    (hdet : ∀ A ∈ S, A.det = 0)
    (hrows : ∀ A ∈ S, ∀ i, A i ∈ D.L)
    (hheight : ∀ A ∈ S, ∀ i, A 2 i ≠ 0)
    (hproj : ∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
      ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
      ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
    (hbound : ∀ A ∈ S, ∀ i j, |A i j| ≤ (2 * N : ℕ))
    (hcap : ∀ A ∈ S, 0 < W A → ∃ T : Set (Fin 3 → ZMod q),
      AuxiliaryCap.IsCap T ∧ ∀ i, (A.map (Int.castRingHom (ZMod q))).col i ∈ T)
    (haffine : ∀ A ∈ S,
      AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col → W A ≤ Ca)
    (hwide : ∀ A ∈ S, W A ≤ Cg * (q : ℝ) ^ 2 * D.h ^ 24)
    (hdistinct : ∀ A ∈ S,
      (∃ i j : Fin 3, (A.map (Int.castRingHom (ZMod q))).col i ≠
        (A.map (Int.castRingHom (ZMod q))).col j) →
      W A ≤ Cd * (q : ℝ) * D.h ^ 12)
    (hexclude : ∀ A ∈ S, ∀ x : Fin 3 → ℤ, IsPrimitive x → A *ᵥ x = 0 →
      AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col →
      0 < W A → D.h ^ 2 < ‖toEuclidean x‖) :
    (∑ A ∈ S, W A) ≤ countConstant Ca Cg Cd * (N : ℝ) ^ 6 /
      (D.I : ℝ) ^ 2 * (Real.log (4 * (N : ℝ)) / Real.log 2) := by
  classical
  let K : ℝ := (1024 * Ca + 3 * (125 * Cg + 512 * Cd)) *
    planeConstant * (N : ℝ) ^ 6 / (D.I : ℝ) ^ 2
  have hK : 0 ≤ K := by dsimp [K, planeConstant]; positivity
  have htotal := PrimitiveNormal.weighted_count_le_log_of_normal_shell_bound
    S W hW hdet hheight hproj (2 * N) (by omega)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbound) hK
  have hshell : ∀ i : ℕ,
      ∑ x ∈ (normalBox (2 * N)).filter (fun x =>
        (2 : ℝ) ^ i ≤ ‖toEuclidean x‖ ∧ ‖toEuclidean x‖ < 2 ^ (i + 1)),
        ∑ A ∈ S.filter (fun A => A *ᵥ x = 0), W A ≤ K := by
    intro i
    let T := (normalBox (2 * N)).filter (fun x =>
      (2 : ℝ) ^ i ≤ ‖toEuclidean x‖ ∧ ‖toEuclidean x‖ < 2 ^ (i + 1))
    let F := fun x => S.filter (fun A => A *ᵥ x = 0)
    have hp : ∀ x ∈ T, IsPrimitive x := by
      intro x hx
      exact ((mem_normalBox _ x).mp (Finset.mem_filter.mp hx).1).1
    have hxne : ∀ x ∈ T, ∀ j, x j ≠ 0 := by
      intro x hx
      exact ((mem_normalBox _ x).mp (Finset.mem_filter.mp hx).1).2.1
    have hn : ∀ x ∈ T, ((2 ^ i : ℕ) : ℝ) ≤ ‖toEuclidean x‖ ∧
        ‖toEuclidean x‖ < 2 * ((2 ^ i : ℕ) : ℝ) := by
      intro x hx
      have hh := (Finset.mem_filter.mp hx).2
      simpa only [Nat.cast_pow, Nat.cast_ofNat, pow_succ, mul_comm] using hh
    have hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ j, A j ∈ D.L := by
      intro x A hA
      exact ⟨(Finset.mem_filter.mp hA).2, hrows A (Finset.mem_filter.mp hA).1⟩
    have hc : ∀ x ∈ T, ∀ A ∈ F x, ∀ j k, |(A j k : ℝ)| ≤ 2 * (N : ℝ) := by
      intro x hx A hA j k
      exact_mod_cast hbound A (Finset.mem_filter.mp hA).1 j k
    have hpr : ∀ x ∈ T, ∀ A ∈ F x, ∃ s t : Fin 3,
        A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
        PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t := by
      intro x hx A hA
      have ha := (Finset.mem_filter.mp hA).1
      exact ⟨0, 1, hheight A ha 0, hheight A ha 1, hproj A ha 0 1 (by decide)⟩
    exact ZeroDeterminantCount.combined_shell_le D q (2 ^ i) hEq hparam T
      (pow_pos (by decide) _) hp hxne hn F hF W (N : ℝ) Ca Cg Cd
      (Nat.cast_nonneg _) hCa hCg hCd
      hc hpr
      (fun x hx A hA => hW A (Finset.mem_filter.mp hA).1)
      (fun x hx A hA hw => hcap A (Finset.mem_filter.mp hA).1 hw)
      (fun x hx A hA ha => haffine A (Finset.mem_filter.mp hA).1 ha)
      (fun x hx A hA ha hw => hexclude A (Finset.mem_filter.mp hA).1 x
        (hp x hx) (Finset.mem_filter.mp hA).2 ha hw)
      (fun x hx A hA => hwide A (Finset.mem_filter.mp hA).1)
      (fun x hx A hA hne => hdistinct A (Finset.mem_filter.mp hA).1 hne)
  have hb := htotal hshell
  convert hb using 1 ; dsimp [K, countConstant] ; push_cast ; ring_nf

end Problem355.ZeroGlobalCount

end

end OAI
