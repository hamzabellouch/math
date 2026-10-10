import OAI.Algebra.Determinantal.BilinearCounts

namespace OAI

namespace PermanentBorder.KernelBilinear
open MvPolynomial Matrix PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {κ J : Type} [Fintype κ] [Fintype J] {n : ℕ}
variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]

theorem selected_kernel_mixed_count
    (F : T → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (ψ : (ℂ × (κ → ℂ)) → T) (h : κ → T)
    (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (B : κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hlocal : ∀ z i j, A₀ i j + ∑ k, A k i j * optionProduct.symm z k = F (ψ z) i j)
    (hdir : ∀ y k i j, fderiv ℂ (fun y => F y i j) y (h k) = B k i j)
    (i : Fin (n+1)) (r : J → Fin (n+1)) (x : J → ChartSpace κ n)
    (hx : Function.Injective (fun j => (x j).1))
    (hz : ∀ j, matrixKernelSystem
      (fun y => (F y).submatrix (pivotEquiv (r j)) (pivotEquiv i)) ψ h (x j) = 0)
    (hs : ∀ j, (fderiv ℂ (matrixKernelSystem
      (fun y => (F y).submatrix (pivotEquiv (r j)) (pivotEquiv i)) ψ h) (x j)).IsInvertible) :
    Fintype.card J ≤
      (Multigraded.mixedPolynomial (firstGroup (κ := κ) (n := n)) secondGroup).coeff
        (dimensions κ n) := by
  classical
  have he (j : J) :
      (fun z => output (r j) (fun a => eval (chart i (r j) z) (system A₀ A B i a))) =
      matrixKernelSystem (fun y => (F y).submatrix (pivotEquiv (r j)) (pivotEquiv i)) ψ h := by
    funext z
    exact system_eq_matrixKernelSystem F ψ h A₀ A B hlocal hdir i (r j) z
  have hz' (j : J) (a : Equations κ n) : eval (chart i (r j) (x j)) (system A₀ A B i a) = 0 := by
    have hh : output (r j) (fun a => eval (chart i (r j) (x j)) (system A₀ A B i a)) =
        output (r j) 0 := by
      rw [map_zero, congrFun (he j) (x j)]
      exact hz j
    exact congrFun ((output (r j)).injective hh) a
  have hc := Multigraded.bilinear_simple_point_count_reindex (dimensions κ n)
    Sigma.fst variablesEquiv variablesEquiv_group firstGroup secondGroup card_equations
    (system A₀ A B i) (system_homogeneous A₀ A B i)
    (fun j => base i (r j)) (fun j => base_group i (r j))
    (fun j => output (r j)) (fun j => chart i (r j)) (fun j => contDiff_chart i (r j))
    (fun j z => chart_base i (r j) z) x
    (fun j k hjk => chart_separated (fun hh => hjk (hx hh))) hz'
    (fun j => by rw [he]; exact hs j)
  exact hc

variable {σ : Type} [Fintype σ]

theorem affine_polar_mixed_count
    (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : σ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (b : σ → ℂ) (L : (Option κ → ℂ) →L[ℂ] (σ → ℂ)) (h : κ → σ → ℂ)
    (x : J → ℂ × (κ → ℂ)) (hx : Function.Injective x)
    (hz : ∀ j, polarPair (fun y => (affine A₀ A y).det)
      (fun z => b + L (optionProduct.symm z)) h (x j) = 0)
    (hs : ∀ j, (fderiv ℂ (polarPair (fun y => (affine A₀ A y).det)
      (fun z => b + L (optionProduct.symm z)) h) (x j)).IsInvertible) :
    Fintype.card J ≤
      (Multigraded.mixedPolynomial (firstGroup (κ := κ) (n := n)) secondGroup).coeff
        (dimensions κ n) := by
  classical
  let ψ := fun z : ℂ × (κ → ℂ) => b + L (optionProduct.symm z)
  obtain ⟨S,hS,hr⟩ := finite_simple_polar_kernel_lifts (0 : Fin (n+1))
    (affine A₀ A) (affine_contDiff A₀ A) ψ h x
    (fun _ => ((differentiable_const b).add (L.differentiable.comp optionProduct.symm.differentiable)).differentiableAt)
    hz hs
  choose r hr using hr
  let A₀' := A₀*S
  let A' := fun v => A v*S
  let B₀ := affine A₀' A' b
  let B := fun k => ∑ v, L (Pi.single k 1) v • A' v
  let D := fun k => ∑ v, h k v • A' v
  have hlocal (z : ℂ × (κ → ℂ)) (i j : Fin (n+1)) :
      B₀ i j + ∑ k, B k i j * optionProduct.symm z k = affine A₀' A' (ψ z) i j := by
    have hexp : optionProduct.symm z = ∑ k, optionProduct.symm z k • Pi.single k 1 := by
      ext k
      simp [Pi.single_apply]
    have hLe (v : σ) : L (optionProduct.symm z) v =
        ∑ k, optionProduct.symm z k * L (Pi.single k 1) v := by
      conv_lhs => rw [hexp, map_sum]
      simp
    simp only [B₀, B, affine, ψ, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, Pi.add_apply, hLe, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    rw [Finset.sum_comm, ← add_assoc]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hd (y : σ → ℂ) (k : κ) (i j : Fin (n+1)) :
      fderiv ℂ (fun y => affine A₀' A' y i j) y (h k) = D k i j := by
    rw [affine_derivative]
    simp [D,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  let X := fun j => matrixKernelPoint
    (fun y => (affine A₀' A' y).submatrix (pivotEquiv (r j)) (pivotEquiv (0 : Fin (n+1)))) ψ (x j)
  apply selected_kernel_mixed_count (affine A₀' A') ψ h B₀ B D hlocal hd 0 r X
  · exact hx
  · intro j
    simpa only [X, A₀', A', affine_right_mul] using (hr j).1
  · intro j
    simpa only [X, A₀', A', affine_right_mul] using (hr j).2

end PermanentBorder.KernelBilinear

end OAI
