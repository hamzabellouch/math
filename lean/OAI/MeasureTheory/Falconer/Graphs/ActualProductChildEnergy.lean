import OAI.MeasureTheory.Falconer.Graphs.ActualProductGraphAssembly
import OAI.MeasureTheory.Falconer.Graphs.ProductEnergyTransfer

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_actual_product_H_child_sum
    {sig c₀ : ℝ} (hsig : 0 < sig) (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi)
    (K : ℕ) (lam T : ℝ) {J : ℕ} (hJ : 0 < J) {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
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
    ∀ (a n : ℕ) (v : ℝ), a+n ≤ N →
    0 ≤ v-(a+n) → (n:ℝ) ≤ v-(a+n)+2*sig*N → (L:ℝ) ≤ v-(a+n)+2*sig*N → v-a ≤ N →
    ∀ e ∈ S 0, ∀ g : ℕ, d 0 e = .parallel g (a+n) →
    a ≤ g → g ≤ a+n → (g:ℝ)-a ≤ 2*sig*N →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let X := (Q 0).descendant A
    let Y := (Q 1).descendant B
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    let M := fun l => ((2:ℝ)^N)^(-mass l (a+n))
    let U := fun z : ℝ × UnitCircle => sourceAngularTransform (ρ 0) X.carrier
      (((2:ℝ)^N)^(-mass 0 a)) (β 0) z.1 z.2
    let V := fun z : ℝ × UnitCircle => sourceAngularTransform (ρ 1) Y.carrier
      (((2:ℝ)^N)^(-mass 1 a)) (β 1) z.1 z.2
    let Uc := fun P : CellPath => fun z : ℝ × UnitCircle =>
      sourceAngularTransform (ρ 0) ((Q 0).descendant P).carrier (M 0) (β 0) z.1 z.2
    let Vc := fun P : CellPath => fun z : ℝ × UnitCircle =>
      sourceAngularTransform (ρ 1) ((Q 1).descendant P).carrier (M 1) (β 1) z.1 z.2
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    (sourceAngularH a v Ψ U V).toReal ≤
      (2:ℝ)^(2*((a:ℝ)+n-a)) * graphProfileCoefficient N ![mass 0,mass 0,mass 1,mass 1] a (a+n) *
      (144*((2:ℝ)^N)^(height (fun t : ℕ => mass 0 t-(t:ℝ)/(N:ℝ)) a (a+n)+2000*(lam+sig)+64*sig)) *
      (∑ row ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n,
        (sourceAngularH (a+n) v Ψ (Uc row.1) (Vc row.2)).toReal) + ((2:ℝ)^N)^(-T) := by
  classical
  obtain ⟨N₁,hgraph⟩ := uniform_actual_product_H_graph hsig hc hcap K lam T hΨ hpos hs
  obtain ⟨N₂,hdegree⟩ := uniform_actual_product_degrees hsig hJ
  obtain ⟨W,hW,hw⟩ := continuous_supported_bump_bound hΨ.continuous hs
  refine ⟨max N₁ N₂,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ ρ mass B δ hd i h hi hh hhb a n v hp hu ht hLu hv
    e he g hdesc hag hgp hgap A B' hA hB
  have hQpos : ∀ l, 0 < (Q l).side := fun l => by rw [hQ l]; norm_num
  have hQle : ∀ l, (Q l).side ≤ 1 := fun l => (hQ l).le
  let : ∀ l, IsProbabilityMeasure (ρ l) := fun l => (hd l).probability
  have hg := hgraph N ((le_max_left _ _).trans hN) S d k hcard hK L hL Q hQpos hQle
    ρ mass B δ hd J i h hh hhb a n v hp hu ht hLu hv A B' hA hB
  let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
  let θ := graphAngularScale N sig (((a+n:ℕ):ℝ)-a) c₀
  let rep := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
    (graphAngularScale_pos N sig (((a+n:ℕ):ℝ)-a) hc) ((min_le_left _ _).trans hcap) false e.2 0 e.1.1 e.1.2
  let I := sourceRetainedProductIndices (Q 0) (Q 1) (ρ 0) (ρ 1) (β 0) (β 1) A B' a n (angularBinCount θ) N sig rep
  have hdeg := hdegree N ((le_max_right _ _).trans hN) (S 0) (d 0) (k 0) (Q 0) (Q 1) (hQ 0) (hQ 1)
    (ρ 0) (ρ 1) (mass 0) lam i hi (h 0) (β 1) e he a g n hdesc hag hgp hp hgap A B' hA hB c₀ hc hcap
  have hIsub : I ⊆ sourceProductGraphIndices ((Q 0).descendant A) ((Q 1).descendant B')
      (ρ 0) (ρ 1) n (angularBinCount θ) A B' :=
    fun _ hmem => (sourceRetainedProductIndices_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmem).1
  have hm (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => β l z.1 z.2) :=
    measurable_inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l) (hh l)
  have hb : ∀ (l : Fin 2) (x : Plane) (dir : UnitCircle), ‖β l x dir‖ ≤ symbolDerivativeConstant K^K := by
    intro l x dir
    exact inheritedCircleSymbol_norm_le (S l) (d l) (k l) (Q l) (hQpos l) (ρ l) (mass l) N lam sig J i (h l)
      K (hK l) x (hhb l x) dir
  have hbound := original_product_graph_integral_bound (Q 0) (Q 1) (ρ 0) (ρ 1) A B' a n hA hB
    (graphAngularScale_pos N sig (((a+n:ℕ):ℝ)-a) hc) I hIsub (by positivity) hdeg
    (M₁ := ((2:ℝ)^N)^(-mass 0 (a+n))) (M₂ := ((2:ℝ)^N)^(-mass 1 (a+n)))
    (by positivity) (by positivity) (β 0) (β 1) (hm 0) (hm 1)
    (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K)
    (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K) (hb 0) (hb 1)
    v hΨ.continuous.measurable hpos hs hW (fun t => (le_abs_self _).trans (hw t))
  dsimp only at hg hbound ⊢
  simp only [Nat.cast_add,β,θ,rep,I,sourceRetainedProductIndices] at hg hbound ⊢
  refine ⟨hg.1,?_⟩
  have hcprof : 0 ≤ graphProfileCoefficient N ![mass 0,mass 0,mass 1,mass 1] a (a+n) :=
    Finset.prod_nonneg (fun _ _ => by positivity)
  have hresult := product_energy_transfer (a:ℝ) ((a:ℝ)+n) v _ _ _ _ hcprof
    ENNReal.toReal_nonneg _ hg.2 hbound
  simpa only [Nat.cast_add,β,θ,rep,I,sourceRetainedProductIndices,mul_assoc] using hresult

end PlanarFalconer

end OAI
