import OAI.MeasureTheory.Falconer.Graphs.ActualDistanceGraphAssembly
import OAI.MeasureTheory.Falconer.Recursion.ParentInactiveRemoval
import OAI.MeasureTheory.Falconer.Recursion.ParentHFBridge

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem complex_two_power_errors {R T x y : ℝ} {z : ℂ} (hR : 2 ≤ R)
    (hxy : |x-y| ≤ R^(-(T+1))) (hyz : ‖(y:ℂ)-z‖ ≤ R^(-(T+1))) :
    ‖(x:ℂ)-z‖ ≤ R^(-T) := by
  have hRp : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have he : R^(-(T+1)) = R^(-T)/R := by
    rw [show -(T+1) = -T-1 by ring,Real.rpow_sub hRp,Real.rpow_one]
  have hc : ‖(x:ℂ)-(y:ℂ)‖ ≤ R^(-(T+1)) := by
    simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hxy
  apply (norm_sub_le_norm_sub_add_norm_sub (x:ℂ) (y:ℂ) z).trans
  apply (add_le_add hc hyz).trans
  rw [he]
  have hp : 0 ≤ R^(-T) := Real.rpow_nonneg hRp.le _
  rw [← two_mul, ← mul_div_assoc]
  apply (div_le_iff₀ hRp).mpr
  nlinarith

theorem uniform_actual_distance_HF_graph
    {sig κ c₀ : ℝ} (hsig : 0 < sig) (hgap : 10*sig < κ)
    (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) (K : ℕ) (lam T : ℝ) (hlam : 0 ≤ lam) (hT : 0 ≤ T)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, (∑ t ∈ S l, k l t) ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (d l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, 0 < (Q l).side) → (∀ l, (Q l).side ≤ 1) →
    ∀ (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ) (B : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l)) →
    ∀ (J i : ℕ) (h : Fin 2 → Plane → ℂ), (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
    ∀ (a n : ℕ) (v : ℝ), a+n ≤ N → κ*N ≤ (n:ℝ) →
    10*sig*N ≤ v-(a+n) → (n:ℝ) ≤ v-(a+n)+2*sig*N → (L:ℝ) ≤ v-(a+n)+2*sig*N → v-a ≤ N →
    ∀ A B : CellPath, A.length = a → B.length = a →
    100*(2:ℝ)^(-(a:ℝ)) ≤ dist ((Q 0).descendant A).center ((Q 1).descendant B).center →
    dist ((Q 0).descendant A).center ((Q 1).descendant B).center ≤ 2000*(2:ℝ)^(-(a:ℝ)) →
    let X := (Q 0).descendant A
    let Y := (Q 1).descendant B
    let t : ℝ := (a+n:ℕ)-a
    let θ := graphAngularScale N sig t c₀
    let I := sourceParentGraphIndices N sig t X Y (ρ 0) (ρ 1) n A B
    let rep := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
      (graphAngularScale_pos N sig t hc) ((min_le_left _ _).trans hcap) true e.2
      (sourceParentAxis X Y) e.1.1 e.1.2
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    let M := fun l => ((2:ℝ)^N)^(-mass l (a+n))
    let F := fun e : GraphNonedgeIndex => graphOriginalTerm ![ρ 0,ρ 1,ρ 1,ρ 0]
      (fun l => (graphQuadCells ![Q 0,Q 1,Q 1,Q 0] e.1 l).carrier)
      ![M 0,M 1,M 1,M 0] ![β 0,β 1,β 1,β 0] true e.2.2 (sourceParentAxis X Y) θ v e.2.1.1 e.2.1.2 Ψ
    ‖((sourceParentHF a v Ψ X Y (ρ 0) (ρ 1)
        (((2:ℝ)^N)^(-mass 0 a)) (((2:ℝ)^N)^(-mass 1 a)) (β 0) (β 1)).toReal : ℂ) -
      ((2:ℝ)^(2*(v-a))) • (graphProfileCoefficient N ![mass 0,mass 1,mass 1,mass 0] a (a+n) •
        (∑ e ∈ graphRetainedIndices I N sig (a+n) true ![Q 0,Q 1,Q 1,Q 0] rep, F e))‖ ≤ ((2:ℝ)^N)^(-T) := by
  classical
  obtain ⟨W,hW,hw⟩ := continuous_supported_bump_bound hΨ.continuous hs
  obtain ⟨N₁,hret⟩ := uniform_actual_retained_distance_graph hsig hgap hc hcap K lam (T+1) hΨ hpos hs
  obtain ⟨N₂,hin⟩ := uniform_parent_inactive_removal hsig hgap (by linarith : 0 ≤ T+1)
    hlam hlam hW K K
  refine ⟨max 1 (max N₁ N₂),?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ hQs ρ mass B δ hd J i h hh hhb a n v
    hp hlow hu ht hLu hv A B' hA hB hlo hsep
  let : ∀ l, IsProbabilityMeasure (ρ l) := fun l => (hd l).probability
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hu0 : 0 ≤ v-(a+n) := (by positivity : (0:ℝ) ≤ 10*sig*N).trans hu
  have hr := hret N hN₁ S d k hcard hK L hL Q hQ hQs ρ mass B δ hd J i h hh hhb
    a n v hp hlow hu0 ht hLu hv A B' hA hB hsep
  let X := (Q 0).descendant A
  let Y := (Q 1).descendant B'
  let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
  have hX : 0 < X.side := (Q 0).descendant_side_pos (hQ 0) A
  have hY : 0 < Y.side := (Q 1).descendant_side_pos (hQ 1) B'
  have hXs : X.side ≤ (2:ℝ)^(-(a:ℝ)) := by
    dsimp [X]; rw [DyadicSquare.descendant_side,hA,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
    simpa only [one_div] using div_le_div_of_nonneg_right (hQs 0) (by positivity : (0:ℝ) ≤ 2^a)
  have hYs : Y.side ≤ (2:ℝ)^(-(a:ℝ)) := by
    dsimp [Y]; rw [DyadicSquare.descendant_side,hB,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
    simpa only [one_div] using div_le_div_of_nonneg_right (hQs 1) (by positivity : (0:ℝ) ≤ 2^a)
  have hi := hin N hN₂ L n a (a+n) v rfl hv (by simpa using hlow) (by simpa using ht) hu hLu
    X Y hX hY hXs hYs hlo hsep Ψ hs hΨ.continuous.measurable
    (fun t => (le_abs_self _).trans (hw t))
    (S 0) (d 0) (k 0) (S 1) (d 1) (k 1) (hcard 0) (hK 0) (hcard 1) (hK 1) (hL 0) (hL 1)
    (Q 0) (Q 1) (hQ 0) (hQ 1) (ρ 0) (ρ 1) (mass 0) (mass 1) J i J i (h 0) (h 1)
    (hh 0) (hh 1) (hhb 0) (hhb 1) (((2:ℝ)^N)^(-mass 0 a)) (((2:ℝ)^N)^(-mass 1 a))
    (by positivity) (by positivity)
    ((hd 0).normalized_cell_mass_le ((Nat.le_add_right a n).trans hp) hA)
    ((hd 1).normalized_cell_mass_le ((Nat.le_add_right a n).trans hp) hB)
  have hm (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => β l z.1 z.2) :=
    measurable_inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l) (hh l)
  have hb : ∀ (l : Fin 2) (x : Plane) (dir : UnitCircle), ‖β l x dir‖ ≤ symbolDerivativeConstant K^K := by
    intro l x dir
    exact inheritedCircleSymbol_norm_le (S l) (d l) (k l) (Q l) (hQ l) (ρ l) (mass l) N lam sig J i (h l)
      K (hK l) x (hhb l x) dir
  have hBnd := pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K
  have hf := sourceParentHF_finite_eq a v Ψ X Y (ρ 0) (ρ 1)
    (M₁ := ((2:ℝ)^N)^(-mass 0 a)) (M₂ := ((2:ℝ)^N)^(-mass 1 a))
    (by positivity) (by positivity) (β 0) (β 1) (hm 0) (hm 1) hBnd hBnd hW (hb 0) (hb 1)
    (fun t => (le_abs_self _).trans (hw t)) (fun t ht => by
      by_contra hn
      have := (hs t hn).2
      linarith)
  dsimp only at hr ⊢
  rw [hf.2]
  apply complex_two_power_errors (R := (2:ℝ)^N) (T := T) ?_ ?_ hr
  · calc
      (2:ℝ) = (2:ℝ)^1 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) ((le_max_left _ _).trans hN)
  · simpa only [Nat.cast_add] using hi

end PlanarFalconer

end OAI
