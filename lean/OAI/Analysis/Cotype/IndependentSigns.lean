import OAI.Analysis.Cotype.QuadraticTypeTensor

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem average_comp_coordinate_embedding {n m : ℕ} (j : Fin n ↪ Fin m)
    (f : Cube n → ℝ) :
    average (fun ζ : Cube m => f (fun i => ζ (j i))) = average f := by
  classical
  let F : Cube m → Cube n → ℝ := fun ζ ε => f (fun i => xor (ζ (j i)) (ε i))
  have hrow (ζ : Cube m) : average (F ζ) = average f := by
    exact average_equiv (signCubeTwist (fun i => ζ (j i))) f
  have hcol (ε : Cube n) : average (fun ζ => F ζ ε) =
      average (fun ζ : Cube m => f (fun i => ζ (j i))) := by
    let σ : Cube m := Function.extend j ε (fun _ => false)
    have hσ i : σ (j i) = ε i := j.injective.extend_apply _ _ _
    have hh := average_equiv (signCubeTwist σ) (fun ζ : Cube m => f (fun i => ζ (j i)))
    simpa only [F,signCubeTwist,Equiv.coe_fn_mk,hσ,Bool.xor_comm] using hh
  calc
    _ = average (fun ε : Cube n => average (fun ζ : Cube m => F ζ ε)) := by
      simp only [hcol,average_const_value]
    _ = average (fun ζ : Cube m => average (F ζ)) := average_comm _
    _ = average f := by simp only [hrow,average_const_value]

theorem rademacherSum_extend {n m : ℕ} (j : Fin n ↪ Fin m) (x : Fin n → X)
    (ζ : Cube m) :
    rademacherSum X (Function.extend j x (fun _ => 0)) ζ =
      rademacherSum X x (fun i => ζ (j i)) := by
  classical
  let y : Fin m → X := Function.extend j x (fun _ => 0)
  have hy i : y (j i) = x i := j.injective.extend_apply _ _ _
  have hz u (hu : u ∉ Finset.univ.image j) : y u = 0 := by
    apply Function.extend_apply'
    simpa using hu
  change (∑ u, sign (ζ u) • y u) = ∑ i, sign (ζ (j i)) • x i
  calc
    _ = ∑ u ∈ Finset.univ.image j, sign (ζ u) • y u :=
      (Finset.sum_subset (Finset.subset_univ _) (fun u _ hu => by rw [hz u hu,smul_zero])).symm
    _ = _ := by rw [Finset.sum_image (fun _ _ _ _ he => j.injective he)]; simp only [hy]

omit [NormedSpace ℝ X] in
theorem sum_norm_sq_extend {n m : ℕ} (j : Fin n ↪ Fin m) (x : Fin n → X) :
    (∑ u, ‖Function.extend j x (fun _ => 0) u‖^2) = ∑ i, ‖x i‖^2 := by
  classical
  let y : Fin m → X := Function.extend j x (fun _ => 0)
  have hy i : y (j i) = x i := j.injective.extend_apply _ _ _
  have hz u (hu : u ∉ Finset.univ.image j) : y u = 0 := by
    apply Function.extend_apply'
    simpa using hu
  change (∑ u, ‖y u‖^2) = ∑ i, ‖x i‖^2
  calc
    _ = ∑ u ∈ Finset.univ.image j, ‖y u‖^2 :=
      (Finset.sum_subset (Finset.subset_univ _) (fun u _ hu => by rw [hz u hu,norm_zero,zero_pow (by norm_num)])).symm
    _ = _ := by rw [Finset.sum_image (fun _ _ _ _ he => j.injective he)]; simp only [hy]

theorem rademacher_sq_extend {n m : ℕ} (j : Fin n ↪ Fin m) (x : Fin n → X) :
    cubeL2 X (rademacherSum X (Function.extend j x (fun _ => 0)))^2 =
      cubeL2 X (rademacherSum X x)^2 := by
  simp only [cubeL2_sq,rademacherSum_extend]
  exact average_comp_coordinate_embedding j (fun ε => ‖rademacherSum X x ε‖^2)

theorem QuadraticTypeBound.mono_dim {n m : ℕ} {A : ℝ}
    (h : QuadraticTypeBound X m A) (hnm : n ≤ m) : QuadraticTypeBound X n A := by
  intro x
  have hh := h (Function.extend (Fin.castLEEmb hnm) x (fun _ => 0))
  simpa only [rademacher_sq_extend,sum_norm_sq_extend] using hh

theorem quadraticTypeBound_le_pow {n : ℕ} {A : ℝ} (hA : 0 ≤ A)
    (h : QuadraticTypeBound X n A) (k : ℕ) {m : ℕ} (hm : m ≤ n^k) :
    QuadraticTypeBound X m (A^k) := (quadraticTypeBound_pow hA h k).mono_dim hm

theorem QuadraticTypeBound.support {m N : ℕ} {A : ℝ}
    (h : QuadraticTypeBound X m A) (s : Finset (Fin N)) (hs : s.card ≤ m)
    (x : Fin N → X) (hx : ∀ i, i ∉ s → x i = 0) :
    cubeL2 X (rademacherSum X x)^2 ≤ A*∑ i, ‖x i‖^2 := by
  classical
  let e : Fin s.card ≃ s := by simpa using (Fintype.equivFin s).symm
  let j : Fin s.card ↪ Fin N := e.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ s))
  let y : Fin s.card → X := fun i => x (j i)
  have he : Function.extend j y (fun _ => 0) = x := by
    funext i
    by_cases hi : i ∈ s
    · obtain ⟨k,hk⟩ := e.surjective ⟨i,hi⟩
      have hj : j k = i := congrArg Subtype.val hk
      rw [← hj,j.injective.extend_apply]
    · have hz : ¬ ∃ k, j k = i := by
        rintro ⟨k,hk⟩
        exact hi (hk ▸ (e k).property)
      rw [Function.extend_apply' _ _ _ hz,hx i hi]
  have hh := h.mono_dim hs y
  rw [← rademacher_sq_extend j y,← sum_norm_sq_extend j y,he] at hh
  exact hh

end Cotype

end

end OAI
