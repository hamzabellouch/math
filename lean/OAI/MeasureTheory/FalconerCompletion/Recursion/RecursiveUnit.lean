import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.BranchTransitions
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Recursion.PolicyDescriptorAnchorGtStart
import OAI.MeasureTheory.FalconerCompletion.Recursion.PrefixDepth
import OAI.MeasureTheory.FalconerCompletion.Recursion.RecursiveEnvironment
import OAI.MeasureTheory.FalconerCompletion.Recursion.ResidualAngularTerminal
import OAI.MeasureTheory.FalconerCompletion.Shells.PrefixParallelMem

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ContDiff Classical
variable {n : ℕ}

noncomputable def recursiveUnit : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))) :=
  ⟨fun _ => 1, by change ContDiff ℝ ∞ (fun _ : EuclideanSpace ℝ (Fin (n+1)) => (1:ℂ)); exact contDiff_const⟩
lemma recursiveUnit_jets (j : ℕ) (w : EuclideanSpace ℝ (Fin (n+1))) :
    ‖iteratedFDeriv ℝ j (recursiveUnit (n:=n)).1 w‖≤1 := by
  cases j with
  | zero => simp [norm_iteratedFDeriv_zero,recursiveUnit]
  | succ j => simp [recursiveUnit,iteratedFDeriv_succ_const]

namespace RecursiveEnvironmentND
noncomputable def angularData (e : RecursiveEnvironmentND n) (a₀ t₀ a v i : ℕ)
    (X Y : CellPath (n+1)) : RecursiveAngularND n :=
  {e with a₀:=a₀,t₀:=t₀,a:=a,v:=v,i:=i,X:=X,Y:=Y}

noncomputable def energies (e : RecursiveEnvironmentND n) (K : ℝ)
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (total : ℕ) (Ψ : ℝ → ℝ) : BranchState → ℝ → Prop
  | .D a t i, x => ∃ X Y : CellPath (n+1), X∈dyadicPaths a ∧ Y∈dyadicPaths a ∧
      0<e.ρ (treeCell X) ∧ 0<e.ρ (treeCell Y) ∧
      farSeparatedGridND a K (fun j => (pathIndex X j:ℤ)) (fun j => (pathIndex Y j:ℤ)) ∧
      x=(e.distanceData a t i X Y).coincidence.toReal
  | .H a₀ t₀ a v i, x => ∃ X Y : CellPath (n+1), X∈dyadicPaths a ∧ Y∈dyadicPaths a ∧
      0<e.ρ (treeCell X) ∧ 0<e.ρ (treeCell Y) ∧
      ∃ (L₁ L₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ),
      Measurable f ∧ Measurable g ∧ (∀ z,‖f z‖≤1) ∧ (∀ z,‖g z‖≤1) ∧
      (∀ b∈policyDescriptorList e.profile e.N e.q a₀ t₀,L₁ b∈W) ∧
      (∀ b∈policyDescriptorList e.profile e.N e.q a₀ t₀,L₂ b∈W) ∧
      (∑ b∈policyDescriptorList e.profile e.N e.q a₀ t₀,(L₁ b).length)≤total ∧
      (∑ b∈policyDescriptorList e.profile e.N e.q a₀ t₀,(L₂ b).length)≤total ∧
      x=(e.angularData a₀ t₀ a v i X Y).energy L₁ L₂ f g recursiveUnit recursiveUnit Ψ
end RecursiveEnvironmentND

lemma RecursiveEnvironmentND.energies_nonneg (e : RecursiveEnvironmentND n) (K : ℝ)
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (total : ℕ) (Ψ : ℝ → ℝ) (hΨ : ∀ r,0≤Ψ r) (s : BranchState) {x : ℝ}
    (hx : e.energies K W total Ψ s x) : 0≤x := by
  cases s with
  | D a t i => obtain ⟨X,Y,hX,hY,hox,hoy,hs,rfl⟩ := hx; exact ENNReal.toReal_nonneg
  | H a₀ t₀ a v i =>
    obtain ⟨X,Y,hX,hY,hox,hoy,L₁,L₂,f,g,hf,hg,hfn,hgn,hL₁,hL₂,ht₁,ht₂,rfl⟩ := hx
    exact _root_.OAI.Attempt4Near.sourceAngularHND_nonneg _ _ _ _ hΨ _ _

lemma unreachedDescriptorList_initial (A : ℕ → ℝ) (N q a t : ℕ) (hq : 0<q) :
    unreachedDescriptorList A N q a t a=policyDescriptorList A N q a t := by
  apply Finset.filter_eq_self.mpr
  intro b hb
  exact policyDescriptor_anchor_gt_start A hq hb

namespace PositiveDistanceState
noncomputable def prefixAngularData (e : PositiveDistanceState (n+1)) (v : ℕ) : RecursiveAngularND n :=
  ⟨⟨e.ρ,e.mass,e.N,e.q,e.J,e.sig,e.C⟩,e.a,e.t,e.a,v,e.i,e.X,e.Y⟩

lemma prefixPhased_symbol (e : PositiveDistanceState (n+1)) (hq : 0<e.q) (v : ℕ)
    (z : PrefixAssignment n) (ξ : EuclideanSpace ℝ (Fin (n+1))) :
    e.prefixPhasedLeft z ξ=(e.prefixAngularData v).symbol (prefixLeftWords z)
      (Attempt4PrefixShell.SpatialFourierND.spatialFourierPhase (n+1) ((2:ℝ)^e.a)⁻¹ ξ) recursiveUnit e.a ∧
    e.prefixPhasedRight z ξ=(e.prefixAngularData v).symbol (prefixRightWords z)
      (Attempt4PrefixShell.SpatialFourierND.spatialFourierPhase (n+1) ((2:ℝ)^e.a)⁻¹ ξ) recursiveUnit e.a := by
  have he := unreachedDescriptorList_initial (adjustedProfile (d:=n+1) e.mass e.N) e.N e.q e.a e.t hq
  constructor <;> ext x w
  · simp only [prefixPhasedLeft,prefixInverseLeft_eq,RecursiveAngularND.symbol,
      actualResidualSourceSymbol,prefixAngularData,RecursiveAngularND.profile,
      RecursiveEnvironmentND.profile,recursiveUnit,one_mul,he,prefixDescriptors]
  · simp only [prefixPhasedRight,prefixInverseRight_eq,RecursiveAngularND.symbol,
      actualResidualSourceSymbol,prefixAngularData,RecursiveAngularND.profile,
      RecursiveEnvironmentND.profile,recursiveUnit,one_mul,he,prefixDescriptors]

lemma prefixGraphChildMax_sameSymbol (e : PositiveDistanceState (n+1)) (hq : 0<e.q) (v : ℕ)
    (Ψ : ℝ → ℝ) (z : PrefixAssignment n) (ξ : EuclideanSpace ℝ (Fin (n+1))) :
    e.prefixGraphChildMax v Ψ z ξ=(e.prefixAngularData v).sameSymbolChildren e.sourcePrefixDepth
      (prefixLeftWords z) (prefixRightWords z)
      (Attempt4PrefixShell.SpatialFourierND.spatialFourierPhase (n+1) ((2:ℝ)^e.a)⁻¹ ξ)
      (Attempt4PrefixShell.SpatialFourierND.spatialFourierPhase (n+1) ((2:ℝ)^e.a)⁻¹ ξ)
      recursiveUnit recursiveUnit Ψ := by
  unfold prefixGraphChildMax
  rw [(e.prefixPhased_symbol hq v z ξ).1,(e.prefixPhased_symbol hq v z ξ).2]
  rfl
end PositiveDistanceState
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ContDiff Classical
variable {n : ℕ}

lemma RecursiveAngularND.reachedChildren_le (e : RecursiveAngularND n) (p : ℕ)
    (L₁ L₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (Q P : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) (Ψ : ℝ → ℝ) (M : ℝ) (hM : 0≤M)
    (hb : ∀ X Y : CellPath (n+1),X∈dyadicPaths p → Y∈dyadicPaths p →
      0<e.ρ (treeCell X) → 0<e.ρ (treeCell Y) →
      (e.successor p X Y).energy L₁ L₂ f g Q P Ψ≤M) :
    e.reachedChildren p L₁ L₂ f g Q P Ψ≤M := by
  unfold reachedChildren _root_.OAI.CurrentFalconer.TreeND.graphSourceChildMax
  split_ifs with hAB
  · apply Finset.sup'_le
    intro z hz
    have hx := Finset.mem_filter.mp (Finset.mem_product.mp hz).1
    have hy := Finset.mem_filter.mp (Finset.mem_product.mp hz).2
    have hh := hb z.1 z.2 ((mem_dyadicPaths p z.1).mpr (_root_.OAI.CurrentFalconer.TreeND.mem_dyadicPaths p z.1 |>.mp (Finset.mem_filter.mp hx.1).1))
      ((mem_dyadicPaths p z.2).mpr (_root_.OAI.CurrentFalconer.TreeND.mem_dyadicPaths p z.2 |>.mp (Finset.mem_filter.mp hy.1).1))
      (by simpa only [_root_.OAI.CurrentFalconer.TreeND.literal_treeCell] using hx.2)
      (by simpa only [_root_.OAI.CurrentFalconer.TreeND.literal_treeCell] using hy.2)
    simp only [RecursiveAngularND.energy,_root_.OAI.CurrentFalconer.TreeND.literal_treeCell] at hh
    convert hh using 1; rfl
  · exact hM

lemma RecursiveAngularND.successor_energy_mem (e : RecursiveAngularND n) (K : ℝ)
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (total : ℕ) (Ψ : ℝ → ℝ) (p : ℕ) (X Y : CellPath (n+1))
    (hX : X∈dyadicPaths p) (hY : Y∈dyadicPaths p)
    (hox : 0<e.ρ (treeCell X)) (hoy : 0<e.ρ (treeCell Y))
    (L₁ L₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hfn : ∀ x,‖f x‖≤1) (hgn : ∀ x,‖g x‖≤1)
    (hw₁ : ∀ b∈e.fullList,L₁ b∈W) (hw₂ : ∀ b∈e.fullList,L₂ b∈W)
    (ht₁ : (∑ b∈e.fullList,(L₁ b).length)≤total) (ht₂ : (∑ b∈e.fullList,(L₂ b).length)≤total) :
    e.toRecursiveEnvironmentND.energies K W total Ψ (.H e.a₀ e.t₀ p e.v e.i)
      ((e.successor p X Y).energy L₁ L₂ f g recursiveUnit recursiveUnit Ψ) :=
  ⟨X,Y,hX,hY,hox,hoy,L₁,L₂,f,g,hf,hg,hfn,hgn,hw₁,hw₂,ht₁,ht₂,rfl⟩

theorem uniform_recursive_high_closure
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (B total Order : ℕ) (hW : ∀ L∈W,L.length≤B)
    (hprefix : prefixInverseVocabulary n Order⊆W) (htotal : 2*Order≤total)
    {sig : ℝ} (hsig : 0<sig) :
    ∃ D : ℝ,1≤D ∧ ∃ N₀ : ℕ, ∀ e : PositiveDistanceState (n+1),
      N₀≤e.N → e.sig=sig → IsFiniteMeasure e.ρ → 0<e.q → e.a≤e.sourcePrefixDepth →
      ∀ (v : ℕ) (Ψ : ℝ → ℝ), Integrable (fun r => Ψ (r/(2:ℝ)^v)) → (∀ r,0≤Ψ r) →
      ∀ K M : ℝ,0≤M →
      (∀ x, (e.prefixAngularData v).toRecursiveEnvironmentND.energies K W total Ψ
        (.H e.a e.t e.sourcePrefixDepth v e.i) x → x≤M) →
      e.prefixHighChildSup Order v Ψ≤D^(4*total)*M := by
  obtain ⟨D,hD,hrem⟩ := uniform_recursive_reached_removal W B total hW hsig 1 (by norm_num)
  obtain ⟨N₀,hrem⟩ := eventually_atTop.mp hrem
  refine ⟨D,hD,N₀,?_⟩
  intro e hN hs hfin hq hap v Ψ hiΨ hΨ K M hM hbound
  apply csSup_le (by exact ⟨0,Set.mem_insert _ _⟩)
  intro r hr
  rcases hr with rfl | ⟨j,hj,z,hz,ξ,rfl⟩
  · positivity
  let a := e.prefixAngularData v
  let f := Attempt4PrefixShell.SpatialFourierND.spatialFourierPhase (n+1) ((2:ℝ)^e.a)⁻¹ ξ
  have hf : Measurable f := by
    exact ((Attempt4PrefixShell.SpatialFourierND.spatialFourierPhase_continuous (n+1)
      ((2:ℝ)^e.a)⁻¹).comp (continuous_const.prodMk continuous_id)).measurable
  have hfn : ∀ x,‖f x‖≤1 := fun x => by
    dsimp only [f]; rw [Attempt4PrefixShell.SpatialFourierND.spatialFourierPhase_norm]
  have hw₁ : ∀ b∈a.fullList,prefixLeftWords z b∈W := fun b _ =>
    hprefix (prefixInverseVocabulary_mem Order j hj _ hz (Sum.inl b))
  have hw₂ : ∀ b∈a.fullList,prefixRightWords z b∈W := fun b _ =>
    hprefix (prefixInverseVocabulary_mem Order j hj _ hz (Sum.inr b))
  have htot := e.prefixInverseWord_total j hz
  have ht₁ : (∑ b∈a.fullList,(prefixLeftWords z b).length)≤total := by
    exact (Nat.le_add_right _ _).trans (htot.trans ((Nat.mul_le_mul_left 2 hj).trans htotal))
  have ht₂ : (∑ b∈a.fullList,(prefixRightWords z b).length)≤total := by
    exact (Nat.le_add_left _ _).trans (htot.trans ((Nat.mul_le_mul_left 2 hj).trans htotal))
  have hb := hrem e.N hN a rfl hs hfin hq e.sourcePrefixDepth hap
    (prefixLeftWords z) (prefixRightWords z) f f recursiveUnit recursiveUnit hf hf hfn hfn
    hw₁ hw₂ ht₁ ht₂ (fun _ _ => by norm_num [recursiveUnit])
    (fun _ _ => by norm_num [recursiveUnit]) Ψ hiΨ hΨ
  rw [e.prefixGraphChildMax_sameSymbol hq v Ψ z ξ]
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply a.reachedChildren_le _ _ _ _ _ _ _ _ M hM
  intro X Y hX hY hox hoy
  exact hbound _ (a.successor_energy_mem K W total Ψ _ X Y hX hY hox hoy
    (prefixLeftWords z) (prefixRightWords z) f f hf hf hfn hfn hw₁ hw₂ ht₁ ht₂)
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical
variable {n : ℕ}

theorem uniform_recursive_terminal
    {Ψ : ℝ → ℝ} (hΨ : Integrable Ψ)
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (B total : ℕ) (hW : ∀ L∈W,L.length≤B) {sig : ℝ} (hsig : 0<sig) :
    ∃ H : ℝ,1≤H ∧ ∃ N₀ : ℕ,0<N₀ ∧ ∀ e : RecursiveEnvironmentND n,
      N₀≤e.N → e.sig=sig → 0<e.q → ∀ B₀ t,RegularizedProfileData e.ρ e.N B₀ t sig e.mass →
      ∀ K : ℝ,∀ s : BranchState,s.Valid e.N sig → s.finish ≤ s.start+100*e.q →
      ∀ x,e.energies K W total Ψ s x →
      x≤H*((2:ℝ)^e.N)^(100*(n+1:ℝ)*(e.q:ℝ)/e.N+4*(n+2:ℝ)*sig) := by
  obtain ⟨H,hH,hbound⟩ := actual_residual_angular_terminal hΨ W B total hW hsig 1 (by norm_num)
  obtain ⟨N₀,hbound⟩ := eventually_atTop.mp hbound
  refine ⟨max 1 H,le_max_left _ _,max 1 N₀,by omega,?_⟩
  intro e hN hs hq B₀ t hd K s hv ht x hx
  let := hd.probability
  have hNp : 0<e.N := by omega
  have hp : 0≤((2:ℝ)^e.N)^(100*(n+1:ℝ)*(e.q:ℝ)/e.N+4*(n+2:ℝ)*sig) := by positivity
  cases s with
  | D a v i =>
    obtain ⟨X,Y,hX,hY,hox,hoy,hsep,rfl⟩ := hx
    have hb := (e.distanceData a v i X Y).actual_distance_terminal_rpow hd hNp
      (hv.1.trans hv.2) ((mem_dyadicPaths a X).mp hX) ((mem_dyadicPaths a Y).mp hY) ht
    apply hb.trans
    apply le_trans _ (le_mul_of_one_le_left hp (le_max_left _ _))
    apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
    change 100*(e.q:ℝ)/e.N+4*((n+1:ℕ)+1:ℝ)*sig≤_
    push_cast
    have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
    have hqn : 100*(e.q:ℝ) ≤ 100*((n:ℝ)+1)*(e.q:ℝ) := by nlinarith [(Nat.cast_nonneg e.q : (0:ℝ)≤(e.q:ℝ))]
    have hh := div_le_div_of_nonneg_right hqn (Nat.cast_nonneg e.N : (0:ℝ)≤(e.N:ℝ))
    linarith
  | H a₀ t₀ a v i =>
    obtain ⟨X,Y,hX,hY,hox,hoy,L₁,L₂,f,g,hf,hg,hfn,hgn,hw₁,hw₂,ht₁,ht₂,rfl⟩ := hx
    have htR : (v:ℝ)-(a:ℝ)≤100*(e.q:ℝ) := by
      have ht' : v≤a+100*e.q := ht
      exact_mod_cast (show (v:ℤ)-(a:ℤ)≤100*(e.q:ℤ) by omega)
    have hh := hbound e.N (by omega) e.ρ e.ρ e.profile e.q a₀ t₀ a hq hNp
      (hv.2.1.trans (hv.2.2.1.trans hv.2.2.2.1)) L₁ L₂ e.mass e.C e.J i f g recursiveUnit recursiveUnit
      X Y v sig t t B₀ B₀ hd hd ((mem_dyadicPaths a X).mp hX) ((mem_dyadicPaths a Y).mp hY)
      htR hf hg hfn hgn hw₁ hw₂ ht₁ ht₂ (fun _ _ => by norm_num [recursiveUnit])
      (fun _ _ => by norm_num [recursiveUnit])
    rw [←hs] at hh
    change _ ≤ max 1 H * _
    have hh' : (e.angularData a₀ t₀ a v i X Y).energy L₁ L₂ f g recursiveUnit recursiveUnit Ψ≤
        H*((2:ℝ)^e.N)^(100*(n+1:ℝ)*e.q/e.N+4*(n+2:ℝ)*sig) := by
      simp only [RecursiveAngularND.energy,_root_.OAI.CurrentFalconer.TreeND.literal_treeCell]
      simp only [_root_.OAI.CurrentFalconer.TreeND.literal_treeCell] at hh
      convert hh using 1 <;> first | rfl | rw [hs]
    exact hh'.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp)
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
