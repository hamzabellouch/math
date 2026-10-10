import OAI.MeasureTheory.Falconer.Graphs.GraphMixedComposition
import OAI.MeasureTheory.Falconer.Angular.ActualStationaryAmplitude

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem complex_periodic_iteratedDeriv {f : ℝ → ℂ} {p : ℝ}
    (hp : Function.Periodic f p) (j : ℕ) : Function.Periodic (iteratedDeriv j f) p := by
  have he : (fun x => f (x+p)) = f := funext hp
  have hh := iteratedDeriv_comp_add_const j f p
  rw [he] at hh
  intro x
  exact (congrFun hh x).symm

theorem graphAngularPullback_angular_deriv (f : ℝ → ℂ) (plus : Bool)
    (p : Plane × ℝ) (c : ℝ) (m : ℕ) :
    iteratedDeriv m (fun t => graphAngularPullback f plus t p) c =
      graphAngularPullback (iteratedDeriv m f) plus c p := by
  simp only [graphAngularPullback, iteratedDeriv_comp_const_add]

theorem uniform_actual_graph_symbol_mixed {sig : ℝ} (hsig : 0 < sig) (K m n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ),
    S.card ≤ (N+1)^3+1 → (∑ a ∈ S, k a) ≤ K →
    ∀ L : ℕ, (∀ a ∈ S, descriptorLength (b a) ≤ L) →
    ∀ Q : DyadicSquare, 0 < Q.side → ∀ (ρ : Measure Plane) (mass : ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Plane → ℂ) (x : Plane), ‖h x‖ ≤ 1 →
    ∀ (plus : Bool) (c : ℝ) (η : Plane) (z : ℝ),
    ‖η‖ ≤ 8 → |z| ≤ 4 → 1/8 ≤ ‖η‖ →
    ‖iteratedFDeriv ℝ n (fun p : Plane × ℝ => iteratedDeriv m
      (fun t => inheritedCircleSymbol S b k Q ρ mass N lam sig J i h x
        (sourceUnitDirection (graphPlaneAngle p.1 +
          (if plus then Real.arctan p.2 else -Real.arctan p.2)+t))) c) (η,z)‖ ≤
      A * sourceSymbolScale N sig L^(m+n) := by
  choose N₀ h₀ using fun j => uniform_actual_symbol_derivatives hsig K j
  let C : ℝ := ∑ j ∈ Finset.range (m+n+1), symbolDerivativeConstant (K+j)^(K+j)
  have hCj (j : ℕ) : 0 ≤ symbolDerivativeConstant (K+j)^(K+j) :=
    pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => hCj j)
  obtain ⟨A,hA,hbound⟩ := graph_mixed_composition_scale n
  refine ⟨A*C,mul_nonneg hA hC, (Finset.range (m+n+1)).sup N₀,?_⟩
  intro N hN ι inst S b k hcard hK L hL Q hQ ρ mass lam J i h x hx plus c η z hhi hz hlo
  let f : ℝ → ℂ := fun θ => inheritedCircleSymbol S b k Q ρ mass N lam sig J i h x
    (sourceUnitDirection θ)
  have hf : ContDiff ℝ ∞ f := inheritedCircleSymbol_contDiff S b k Q hQ ρ mass N lam sig J i h x
  have hp : Function.Periodic f (2*Real.pi) := by
    intro θ
    dsimp [f]
    rw [sourceUnitDirection_periodic]
  have hsmooth : ∀ q : ℕ, ContDiff ℝ ∞ (iteratedDeriv q f) := by
    intro q
    induction q with
    | zero => simpa using hf
    | succ q ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2
  have hfder := hsmooth m
  have hDpos := sourceSymbolScale_pos N sig L
  have hb : ∀ j ≤ n, ∀ θ, ‖iteratedDeriv j (iteratedDeriv m f) θ‖ ≤
      (C*sourceSymbolScale N sig L^m)*sourceSymbolScale N sig L^j := by
    intro j hj θ
    have hiter : iteratedDeriv j (iteratedDeriv m f) = iteratedDeriv (j+m) f := by
      simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]
    rw [hiter]
    have hjmem : j+m ∈ Finset.range (m+n+1) := Finset.mem_range.mpr (by omega)
    have hNj : N₀ (j+m) ≤ N := (Finset.le_sup hjmem).trans hN
    have he := h₀ (j+m) N hNj S b k hcard hK L hL Q hQ ρ mass lam J i h x hx θ
    calc
      _ ≤ symbolDerivativeConstant (K+(j+m))^(K+(j+m))*sourceSymbolScale N sig L^(j+m) := he
      _ ≤ C*sourceSymbolScale N sig L^(j+m) := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun l _ => hCj l) hjmem) (by positivity)
      _ = _ := by rw [pow_add]; ring
  have he := hbound (iteratedDeriv m f) hfder (complex_periodic_iteratedDeriv hp m)
    (C*sourceSymbolScale N sig L^m) (sourceSymbolScale N sig L) (by positivity)
    (sourceSymbolScale_one_le N hsig.le L) hb plus c η z hhi hz hlo
  change ‖iteratedFDeriv ℝ n (fun p : Plane × ℝ => iteratedDeriv m
    (fun t => f (graphPlaneAngle p.1 +
      (if plus then Real.arctan p.2 else -Real.arctan p.2)+t)) c) (η,z)‖ ≤ _
  simp only [iteratedDeriv_comp_const_add]
  convert he using 1
  · rfl
  · rw [pow_add]; ring

end PlanarFalconer

end OAI
