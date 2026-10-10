import OAI.Geometry.PeriodicTiling.ConfigurationDifferenceReduction
import OAI.Geometry.PeriodicTiling.ForwardDifference
import OAI.Geometry.PeriodicTiling.FiniteMasks
import OAI.Geometry.PeriodicTiling.PlaneLattices
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith

namespace OAI

universe uB

namespace PeriodicTilingThree

theorem forwardDiff_slice {B : Type uB} [AddCommGroup B]
    (f : Plane → B) (x e : Plane) :
    forwardDiff (fun n : ℤ => f (x + n • e)) =
      fun n => configDiff e f (x + n • e) := by
  ext n
  simp only [forwardDiff_apply, configDiff_apply, add_zsmul, one_zsmul, add_assoc]

theorem forwardDiff_iterate_slice {B : Type uB} [AddCommGroup B]
    (k : ℕ) (f : Plane → B) (x e : Plane) :
    (forwardDiff^[k]) (fun n : ℤ => f (x + n • e)) =
      fun n => ((configDiff e)^[k] f) (x + n • e) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, forwardDiff_slice, ih,
        Function.iterate_succ_apply]

theorem circle_sum_of_indicator_decomposition {m : ℕ} (A : Set Plane)
    (φ : Fin m → Plane → ℝ)
    (hsum : ∀ x, tileIndicator ℝ A x + ∑ j, φ j x = 1) :
    (∑ j, (fun x => (φ j x : AddCircle (1 : ℝ)))) = fun _ => 0 := by
  classical
  ext x
  simp only [Finset.sum_apply]
  change (∑ j, (φ j x : AddCircle (1 : ℝ))) = 0
  have hcast : (∑ j, (φ j x : AddCircle (1 : ℝ))) =
      ((∑ j, φ j x : ℝ) : AddCircle (1 : ℝ)) := by
    exact (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
      (fun j => φ j x) Finset.univ).symm
  rw [hcast, show (∑ j, φ j x) = 1 - tileIndicator ℝ A x by linarith [hsum x]]
  by_cases hx : x ∈ A <;> simp [tileIndicator, hx, AddCircle.coe_period]

theorem directional_circle_slice_polynomial {m : ℕ} (hm : 0 < m)
    (A : Set Plane) (v : Fin m → Plane) (φ : Fin m → Plane → ℝ)
    (e : Plane)
    (hspan : ∀ i j, i ≠ j → ∃ a b : ℤ, e = a • v i + b • v j)
    (hp : ∀ j, Function.Periodic (φ j) (v j))
    (hsum : ∀ x, tileIndicator ℝ A x + ∑ j, φ j x = 1)
    (j : Fin m) (x : Plane) :
    (forwardDiff^[m]) (fun n : ℤ =>
      (φ j (x + n • e) : AddCircle (1 : ℝ))) = 0 := by
  classical
  let ψ : Fin m → Plane → AddCircle (1 : ℝ) := fun i y => (φ i y : AddCircle (1 : ℝ))
  have hψ : ∀ i, Function.Periodic (ψ i) (v i) := by
    intro i y
    change (φ i (y + v i) : AddCircle (1 : ℝ)) = (φ i y : AddCircle (1 : ℝ))
    rw [hp i y]
  have hrep : ∀ i : Fin m, ∃ a b : ℤ, i = j ∨ e = a • v i + b • v j := by
    intro i
    by_cases hij : i = j
    · exact ⟨0, 0, Or.inl hij⟩
    · obtain ⟨a, b, hab⟩ := hspan i j hij
      exact ⟨a, b, Or.inr hab⟩
  choose α β hrep using hrep
  let u : Fin m → Plane := fun i => if i = j then e else α i • v i
  let vs : List Plane := Finset.univ.toList.map u
  have hlen : vs.length = m := by simp [vs]
  have hne : vs ≠ [] := by
    intro h
    have hz : m = 0 := by simpa only [h, List.length_nil] using hlen.symm
    exact (Nat.ne_of_gt hm) hz
  have hkill : ∀ i, i ≠ j → ∃ w ∈ vs, Function.Periodic (ψ i) w := by
    intro i hij
    refine ⟨u i, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨i, by simp, rfl⟩
    · simpa only [u, ite_eq_right hij] using (hψ i).zsmul (α i)
  have hz : configDiffs vs (ψ j) = 0 :=
    configDiffs_component_zero j vs hne ψ 0
      (circle_sum_of_indicator_decomposition A φ hsum) hkill
  have hreplace : ∀ w ∈ vs, ∃ k : ℤ, w = e + k • v j := by
    intro w hw
    obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hw
    by_cases hij : i = j
    · refine ⟨0, ?_⟩
      simp [u, hij]
    · refine ⟨-β i, ?_⟩
      have he := (hrep i).resolve_left hij
      simp only [u, ite_eq_right hij, he, neg_smul]
      abel
  rw [configDiffs_eq_iterate_of_period vs e (v j) (ψ j) (hψ j) hreplace,
    hlen] at hz
  change (forwardDiff^[m]) (fun n : ℤ => ψ j (x + n • e)) = 0
  rw [forwardDiff_iterate_slice, hz]
  rfl

theorem directional_slice_pair_bound {m : ℕ} (A : Set Plane)
    (v : Fin m → Plane) (φ : Fin m → Plane → ℝ) (e : Plane)
    (hspan : ∀ i j, i ≠ j → ∃ a b : ℤ, e = a • v i + b • v j)
    (hφ : ∀ j x, 0 ≤ φ j x)
    (hp : ∀ j, Function.Periodic (φ j) (v j))
    (hsum : ∀ x, tileIndicator ℝ A x + ∑ j, φ j x = 1)
    (x : Plane) (i j : Fin m) (hij : i ≠ j) (n r : ℤ) :
    φ i (x + n • e) + φ j (x + r • e) ≤ 1 := by
  classical
  obtain ⟨a, b, he⟩ := hspan i j hij
  let y : Plane := x + n • e + ((r - n) * a) • v i
  have hy : y = x + r • e + ((n - r) * b) • v j := by
    dsimp [y]
    rw [he]
    simp only [smul_add, mul_smul, sub_smul]
    abel
  have hi : φ i y = φ i (x + n • e) :=
    (hp i).zsmul ((r - n) * a) _
  have hj : φ j y = φ j (x + r • e) := by
    rw [hy]
    exact (hp j).zsmul ((n - r) * b) _
  have hle : φ i y + φ j y ≤ ∑ k, φ k y := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({i, j} : Finset (Fin m)))
      (fun k _hk _hnot => hφ k y)
    simpa [hij] using h
  have htotal := hsum y
  have ha := tileIndicator_nonneg A y
  rw [hi, hj] at hle
  linarith

end PeriodicTilingThree

end OAI
