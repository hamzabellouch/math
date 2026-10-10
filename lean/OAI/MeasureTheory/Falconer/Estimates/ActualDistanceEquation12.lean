import OAI.MeasureTheory.Falconer.Estimates.ActualDistanceEstimate

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_actual_distance_equation12
    {sig κ c₀ : ℝ} (hsig : 0 < sig) (hgap : 10*sig < κ) (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi)
    (K : ℕ) (lam T : ℝ) (hlam : 0 ≤ lam) (hT : 0 ≤ T) {η : ℝ} (hη : 0 < η) {J : ℕ} (hJ : 0 < J) {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ t, 0 ≤ Ψ t) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, (∑ t ∈ S l, k l t) ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (d l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ) (B : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l)) →
    ∀ (i : ℕ) (h : Fin 2 → Plane → ℂ), i < J → (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
    ∀ (a n : ℕ) (v : ℝ), a+n ≤ N → κ*N ≤ (n:ℝ) →
    10*sig*N ≤ v-(a+n) → (n:ℝ) ≤ v-(a+n)+2*sig*N → (L:ℝ) ≤ v-(a+n)+2*sig*N → v-a ≤ N →
    ∀ e : ∀ l, ι l, (∀ l, e l ∈ S l) → (∀ l, d l (e l) = .parallel a (a+n)) →
    ∀ A B : CellPath, A.length = a → B.length = a →
    100*(2:ℝ)^(-(a:ℝ)) ≤ dist ((Q 0).descendant A).center ((Q 1).descendant B).center →
    dist ((Q 0).descendant A).center ((Q 1).descendant B).center ≤ 2000*(2:ℝ)^(-(a:ℝ)) →
    let X := (Q 0).descendant A
    let Y := (Q 1).descendant B
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    let M := fun l => ((2:ℝ)^N)^(-mass l (a+n))
    let Uc := fun P : CellPath => fun z : ℝ × UnitCircle =>
      sourceAngularTransform (ρ 0) ((Q 0).descendant P).carrier (M 0) (β 0) z.1 z.2
    let Vc := fun P : CellPath => fun z : ℝ × UnitCircle =>
      sourceAngularTransform (ρ 1) ((Q 1).descendant P).carrier (M 1) (β 1) z.1 z.2
    sourceParentHF a v Ψ X Y (ρ 0) (ρ 1) (((2:ℝ)^N)^(-mass 0 a)) (((2:ℝ)^N)^(-mass 1 a)) (β 0) (β 1) ≠ ⊤ ∧
    (sourceParentHF a v Ψ X Y (ρ 0) (ρ 1) (((2:ℝ)^N)^(-mass 0 a)) (((2:ℝ)^N)^(-mass 1 a)) (β 0) (β 1)).toReal ≤
      ((2:ℝ)^N)^(
        -(mass 0 (a+n)-((a:ℝ)+n)/N-(mass 0 a-(a:ℝ)/N))
        -(mass 1 (a+n)-((a:ℝ)+n)/N-(mass 1 a-(a:ℝ)/N))
        +min (height (fun t : ℕ => mass 0 t-(t:ℝ)/(N:ℝ)) a (a+n))
          (height (fun t : ℕ => mass 1 t-(t:ℝ)/(N:ℝ)) a (a+n))+4000*(lam+sig)+η) *
      finiteEnergyMaximum (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n)
        (fun row => sourceAngularH (a+n) v Ψ (Uc row.1) (Vc row.2)) + ((2:ℝ)^N)^(-T) := by
  classical
  obtain ⟨N₁,hfixed⟩ := uniform_actual_distance_equation12_fixed hsig hgap hc hcap K lam T hlam hT hJ hΨ hpos hs
  obtain ⟨N₂,hconst⟩ := fixed_constant_absorbed hη (589824:ℝ)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ ρ mass B δ hd i h hi hh hhb a n v hp hlow hu ht hLu hv
    e he hdesc A B' hA hB hlo hsep
  have hg := hfixed N ((le_max_left _ _).trans hN) S d k hcard hK L hL Q hQ ρ mass B δ hd
    i h hi hh hhb a n v hp hlow hu ht hLu hv e he hdesc A B' hA hB hlo hsep
  have hcoef (x : ℝ) : 589824*((2:ℝ)^N)^x ≤ ((2:ℝ)^N)^(x+η) := by
    rw [Real.rpow_add (by positivity : (0:ℝ)<(2:ℝ)^N)]
    nlinarith [mul_le_mul_of_nonneg_right (hconst N ((le_max_right _ _).trans hN))
      (by positivity : (0:ℝ) ≤ ((2:ℝ)^N)^x)]
  dsimp only at hg ⊢
  refine ⟨hg.1,hg.2.trans ?_⟩
  exact add_le_add (mul_le_mul_of_nonneg_right (hcoef _) (finiteEnergyMaximum_nonneg _ _)) (le_refl _)

end PlanarFalconer

end OAI
