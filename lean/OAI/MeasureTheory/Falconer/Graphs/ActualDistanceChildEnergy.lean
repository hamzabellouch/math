import OAI.MeasureTheory.Falconer.Graphs.ActualDistanceHFGraph
import OAI.MeasureTheory.Falconer.Graphs.DistanceGraphIntegral
import OAI.MeasureTheory.Falconer.Graphs.ProductEnergyTransfer

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_actual_distance_HF_child_sum
    {sig κ c₀ : ℝ} (hsig : 0 < sig) (hgap : 10*sig < κ) (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi)
    (K : ℕ) (lam T : ℝ) (hlam : 0 ≤ lam) (hT : 0 ≤ T) {J : ℕ} (hJ : 0 < J) {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
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
      (2:ℝ)^(2*((a:ℝ)+n-a)) * graphProfileCoefficient N ![mass 0,mass 1,mass 1,mass 0] a (a+n) *
      (144*((2:ℝ)^N)^(min (height (fun t : ℕ => mass 0 t-(t:ℝ)/(N:ℝ)) a (a+n))
        (height (fun t : ℕ => mass 1 t-(t:ℝ)/(N:ℝ)) a (a+n))+2000*(lam+sig)+60*sig)) *
      (∑ row ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n,
        (sourceAngularH (a+n) v Ψ (Uc row.1) (Vc row.2)).toReal) + ((2:ℝ)^N)^(-T) := by
  classical
  obtain ⟨N₁,hgraph⟩ := uniform_actual_distance_HF_graph hsig hgap hc hcap K lam T hlam hT hΨ hpos hs
  obtain ⟨N₂,hdegree⟩ := uniform_actual_distance_degrees hsig hgap hc hcap hJ
  obtain ⟨N₃,hscale⟩ := graphAngularScale_cap_inactive hgap hc
  obtain ⟨W,hW,hw⟩ := continuous_supported_bump_bound hΨ.continuous hs
  refine ⟨max N₁ (max N₂ N₃),?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ ρ mass B δ hd i h hi hh hhb a n v hp hlow hu ht hLu hv
    e he hdesc A B' hA hB hlo hsep
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN₂ : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₃ : N₃ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hQpos : ∀ l, 0 < (Q l).side := fun l => by rw [hQ l]; norm_num
  have hQle : ∀ l, (Q l).side ≤ 1 := fun l => (hQ l).le
  let : ∀ l, IsProbabilityMeasure (ρ l) := fun l => (hd l).probability
  have hg := hgraph N hN₁ S d k hcard hK L hL Q hQpos hQle
    ρ mass B δ hd J i h hh hhb a n v hp hlow hu ht hLu hv A B' hA hB hlo hsep
  let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
  let t : ℝ := (a+n:ℕ)-a
  let θ := graphAngularScale N sig t c₀
  let axis := sourceParentAxis ((Q 0).descendant A) ((Q 1).descendant B')
  let rep := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
    (graphAngularScale_pos N sig t hc) ((min_le_left _ _).trans hcap) true e.2 axis e.1.1 e.1.2
  let I := sourceRetainedDistanceIndices (Q 0) (Q 1) (ρ 0) (ρ 1) (β 0) (β 1) A B' a n N sig t θ rep
  have hsc : θ = graphUncappedAngularScale N sig t := hscale N hN₃ t (by simpa [t] using hlow)
  have hdeg := hdegree N hN₂ S d k Q hQ ρ mass lam i hi h e he a n hdesc hp hlow A B' hA hB hsep
  have hIsub : I ⊆ sourceParentGraphIndices N sig t ((Q 0).descendant A) ((Q 1).descendant B')
      (ρ 0) (ρ 1) n A B' :=
    fun _ hmem => (sourceRetainedDistanceIndices_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmem).1
  have hm (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => β l z.1 z.2) :=
    measurable_inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l) (hh l)
  have hb : ∀ (l : Fin 2) (x : Plane) (dir : UnitCircle), ‖β l x dir‖ ≤ symbolDerivativeConstant K^K := by
    intro l x dir
    exact inheritedCircleSymbol_norm_le (S l) (d l) (k l) (Q l) (hQpos l) (ρ l) (mass l) N lam sig J i (h l)
      K (hK l) x (hhb l x) dir
  have hBnd := pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K
  have hfin := (sourceParentHF_finite_eq a v Ψ ((Q 0).descendant A) ((Q 1).descendant B') (ρ 0) (ρ 1)
    (M₁ := ((2:ℝ)^N)^(-mass 0 a)) (M₂ := ((2:ℝ)^N)^(-mass 1 a))
    (by positivity) (by positivity) (β 0) (β 1) (hm 0) (hm 1) hBnd hBnd hW (hb 0) (hb 1)
    (fun t => (le_abs_self _).trans (hw t)) (fun t ht => by
      by_contra hn
      have := (hs t hn).2
      linarith)).1
  have hbound := original_distance_graph_integral_bound (Q 0) (Q 1) (ρ 0) (ρ 1) A B' N a n sig t hA hB
    (graphAngularScale_pos N sig t hc) hsc axis I hIsub (by positivity) hdeg
    (M₁ := ((2:ℝ)^N)^(-mass 0 (a+n))) (M₂ := ((2:ℝ)^N)^(-mass 1 (a+n)))
    (by positivity) (by positivity) (β 0) (β 1) (hm 0) (hm 1)
    hBnd hBnd (hb 0) (hb 1) v hΨ.continuous.measurable hpos hs hW
    (fun t => (le_abs_self _).trans (hw t))
  have heq := sourceRetainedDistance_original_sum (Q 0) (Q 1) A B' N a n sig t θ v hsc
    (ρ 0) (ρ 1) (((2:ℝ)^N)^(-mass 0 (a+n))) (((2:ℝ)^N)^(-mass 1 (a+n))) (β 0) (β 1) Ψ rep
  dsimp only at hg hbound heq ⊢
  rw [graphOriginalDistanceSum_supported] at hbound
  rw [heq] at hg
  refine ⟨hfin,?_⟩
  have hcprof : 0 ≤ graphProfileCoefficient N ![mass 0,mass 1,mass 1,mass 0] a (a+n) :=
    Finset.prod_nonneg (fun _ _ => by positivity)
  have hresult := product_energy_transfer (a:ℝ) ((a:ℝ)+n) v _ _ _ _ hcprof
    ENNReal.toReal_nonneg _ hg hbound
  simpa only [Nat.cast_add,β,θ,t,axis,rep,I,sourceRetainedDistanceIndices,mul_assoc] using hresult

end PlanarFalconer

end OAI
