import OAI.MeasureTheory.Falconer.Estimates.ActualProductEstimate

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_actual_product_equation13
    {sig c₀ : ℝ} (hsig : 0 < sig) (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi)
    (K : ℕ) (lam T : ℝ) (hlam : 0 ≤ lam) {η : ℝ} (hη : 0 < η) {J : ℕ} (hJ : 0 < J) {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ t, 0 ≤ Ψ t) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, (∑ t ∈ S l, k l t) ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (d l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) (mass : ℝ → ℝ) (B : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam mass) →
    ∀ (i : ℕ) (h : Fin 2 → Plane → ℂ), i < J → (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
    ∀ (a n : ℕ) (v : ℝ), a+n ≤ N →
    0 ≤ v-(a+n) → (n:ℝ) ≤ v-(a+n)+2*sig*N → (L:ℝ) ≤ v-(a+n)+2*sig*N → v-a ≤ N →
    ∀ e ∈ S 0, ∀ g : ℕ, d 0 e = .parallel g (a+n) →
    a ≤ g → g ≤ a+n → (g:ℝ)-a ≤ 2*sig*N →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let X := (Q 0).descendant A
    let Y := (Q 1).descendant B
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) mass N lam sig J i (h l)
    let M := fun _ : Fin 2 => ((2:ℝ)^N)^(-mass (a+n))
    let U := fun z : ℝ × UnitCircle => sourceAngularTransform (ρ 0) X.carrier
      (((2:ℝ)^N)^(-mass a)) (β 0) z.1 z.2
    let V := fun z : ℝ × UnitCircle => sourceAngularTransform (ρ 1) Y.carrier
      (((2:ℝ)^N)^(-mass a)) (β 1) z.1 z.2
    let Uc := fun P : CellPath => fun z : ℝ × UnitCircle =>
      sourceAngularTransform (ρ 0) ((Q 0).descendant P).carrier (M 0) (β 0) z.1 z.2
    let Vc := fun P : CellPath => fun z : ℝ × UnitCircle =>
      sourceAngularTransform (ρ 1) ((Q 1).descendant P).carrier (M 1) (β 1) z.1 z.2
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    (sourceAngularH a v Ψ U V).toReal ≤
      ((2:ℝ)^N)^(
        -2*(mass (a+n)-((a:ℝ)+n)/N-(mass a-(a:ℝ)/N))
        +height (fun t : ℕ => mass t-(t:ℝ)/(N:ℝ)) a (a+n)+4000*(lam+sig)+η) *
      finiteEnergyMaximum (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n)
        (fun row => sourceAngularH (a+n) v Ψ (Uc row.1) (Vc row.2)) + ((2:ℝ)^N)^(-T) := by
  obtain ⟨N₀,hmain⟩ := uniform_actual_product_estimate hsig hc hcap K lam T hlam hη hJ hΨ hpos hs
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ ρ mass B δ hd i h hi hh hhb a n v hp hu ht hLu hv
    e he g hdesc hag hgp hgap A B' hA hB
  have hh' := hmain N hN S d k hcard hK L hL Q hQ ρ (fun _ => mass) B δ hd
    i h hi hh hhb a n v hp hu ht hLu hv e he g hdesc hag hgp hgap A B' hA hB
  dsimp only at hh' ⊢
  have heq (x : ℝ) : -x-x = -2*x := by ring
  simpa only [heq] using hh'

end PlanarFalconer

end OAI
