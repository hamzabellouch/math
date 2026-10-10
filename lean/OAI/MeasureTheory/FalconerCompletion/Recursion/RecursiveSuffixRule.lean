import Mathlib
import OAI.MeasureTheory.Falconer.Estimates.ActualFarBuffer
import OAI.MeasureTheory.Falconer.Geometry.BinBands
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.BranchTransitions
import OAI.MeasureTheory.Falconer.Recursion.InteriorPolicy
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Angular.PowerDivCap
import OAI.MeasureTheory.FalconerCompletion.Recursion.OccupiedDescendantPath
import OAI.MeasureTheory.FalconerCompletion.Recursion.RecursiveUnit
import OAI.MeasureTheory.FalconerCompletion.Shells.PrefixHighShell

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical
variable {n : ℕ}

theorem uniform_recursive_suffix_rule {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J) :
    ∃ H : ℝ,0≤H ∧ ∃ N₀ : ℕ,∀ e : RecursiveEnvironmentND n,
      N₀≤e.N → e.sig=sig → e.J=J → IsFiniteMeasure e.ρ → 0<e.q →
      ∀ (K : ℝ),1000*(n+2:ℝ)<K →
      ∀ (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
        (total _offset a t i : ℕ) (Ψ : ℝ → ℝ) (eps : ℝ), 0≤eps → i<e.J → t≤e.N → a+100*e.q<t →
      a+t<2*policyDepth e.profile e.N e.q a t →
      ∀ M : ℝ, (∀ x,e.energies K W total Ψ (.D a (policyDepth e.profile e.N e.q a t) (i+1)) x →
        ((2:ℝ)^e.N)^(DimensionalPolicy.branchExponentND e.profile (recursiveLoss n e.C) sig sig eps
          (.D a t i) .suffix (.D a (policyDepth e.profile e.N e.q a t) (i+1)))*x≤M) →
      ∀ x,e.energies K W total Ψ (.D a t i) x → x≤H*M := by
  obtain ⟨N₀,hsuff⟩ := PositiveDistanceState.uniform_actual_suffix_reduction (d:=n+1) hsig hJ
  let H : ℝ := ((bandOffsets (100*(n+2:ℝ))).card:ℝ)*((bandOffsets 3).card:ℝ)
  refine ⟨H,by dsimp [H]; positivity,N₀,?_⟩
  intro e hN he hJe hfin hq K hK W total offset a t i Ψ eps heps hi ht hw hside M hbound x hx
  let := hfin
  obtain ⟨X,Y,hX,hY,hox,hoy,hsep,rfl⟩ := hx
  let f := e.distanceData a t i X Y
  let p := policyDepth e.profile e.N e.q a t
  let g := e.distanceData a p (i+1) X Y
  let : IsFiniteMeasure g.ρ := hfin
  have hf := hsuff f he hJe hN hfin K (by convert hK using 1; push_cast; ring)
    (farSeparated_centre ((mem_dyadicPaths a X).mp hX) ((mem_dyadicPaths a Y).mp hY) hsep)
    ((mem_dyadicPaths a X).mp hX) ((mem_dyadicPaths a Y).mp hY) hq (by exact Nat.succ_le_of_lt hi) ht hw hside
  have hreal := ENNReal.toReal_mono (by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · exact ENNReal.mul_ne_top (by simp) (by simp)
      · exact ENNReal.ofReal_ne_top
    · exact g.coincidence_ne_top) hf
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast] at hreal
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  have hcap := hbound g.coincidence.toReal (e.distance_mem K W total Ψ a p (i+1) X Y hX hY hox hoy hsep)
  have hexp : e.profile p-intervalMin e.profile p t+e.C*sig≤
      DimensionalPolicy.branchExponentND e.profile (recursiveLoss n e.C) sig sig eps
        (.D a t i) .suffix (.D a p (i+1)) := by
    simp only [DimensionalPolicy.branchExponentND,DimensionalPolicy.branchCost,BranchState.start,BranchState.finish]
    have hh := mul_le_mul_of_nonneg_right (recursiveLoss_test n e.C) hsig.le
    simp only [show BranchLabel.suffix ≠ .low by decide,↓reduceIte]
    nlinarith
  have hb := weighted_child_cap ENNReal.toReal_nonneg hexp hcap
  have hf' : f.coincidence.toReal≤H*(((2:ℝ)^e.N)^(e.profile p-intervalMin e.profile p t+e.C*sig)*g.coincidence.toReal) := by
    convert hreal using 1; simp only [H,f,g,RecursiveEnvironmentND.distanceData,RecursiveEnvironmentND.profile,p]; push_cast; ring_nf
  exact hf'.trans (mul_le_mul_of_nonneg_left hb (by dsimp [H]; positivity))
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
theorem prefix_high_weighted_cap {sig : ℝ} (hsig : 0<sig)
    (e : RecursiveEnvironmentND n) (he : e.sig=sig) [IsFiniteMeasure e.ρ]
    (a t i offset Order total : ℕ) (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (X Y : CellPath (n+1)) (K eps D M : ℝ) (hD : 1≤D) (hM : 0≤M)
    (Ψ : ℝ → ℝ) (_hiΨ : Integrable Ψ) (_hΨ0 : ∀ r,0≤Ψ r)
    (_hq : 0<e.q) (_ht : t≤e.N) (hw : a+100*e.q<t)
    (hside : 2*policyDepth e.profile e.N e.q a t≤a+t)
    (hchildren : ∀ u l,DimensionalPolicy.BranchStep e.profile e.N e.q offset sig (.D a t i) l u →
      ∀ x,e.energies K W total Ψ u x →
      ((2:ℝ)^e.N)^(DimensionalPolicy.branchExponentND e.profile (recursiveLoss n e.C) sig sig eps (.D a t i) l u)*x≤M)
    (hclose : ∀ (v : ℕ) (M : ℝ),0≤M →
      (∀ x,((e.distanceData a t i X Y).prefixAngularData v).toRecursiveEnvironmentND.energies K W total Ψ
        (.H a t (policyDepth e.profile e.N e.q a t) v i) x → x≤M) →
      (e.distanceData a t i X Y).prefixHighChildSup Order v Ψ≤D^(4*total)*M)
    (j : ℕ) (hj : j∈(e.distanceData a t i X Y).prefixHighIndices) :
    ((2:ℝ)^e.N)^eps*(e.distanceData a t i X Y).prefixGraphFactor*
      (e.distanceData a t i X Y).prefixHighChildSup Order (j+1:ℕ) Ψ≤D^(4*total)*M := by
  let p := policyDepth e.profile e.N e.q a t
  have hjm := Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1
  have hj' := (e.distanceData a t i X Y).prefixHighIndices_spec hj
  let u := BranchState.H a t p (j+1) i
  let expo := DimensionalPolicy.branchExponentND e.profile (recursiveLoss n e.C) sig sig eps (.D a t i) .high u
  have hstep : DimensionalPolicy.BranchStep e.profile e.N e.q offset sig (.D a t i) .high u :=
    .high hw hside (Finset.mem_Ioc.mpr (by dsimp [RecursiveEnvironmentND.distanceData] at hjm; omega)) (by simpa only [RecursiveEnvironmentND.distanceData,he] using hj'.2)
  have hcap : ∀ x,((e.distanceData a t i X Y).prefixAngularData (j+1)).toRecursiveEnvironmentND.energies K W total Ψ u x → x≤M/((2:ℝ)^e.N)^expo := by
    intro y hy
    exact (le_div_iff₀ (by positivity : 0<((2:ℝ)^e.N)^expo)).mpr (by
      simpa only [mul_comm] using hchildren _ _ hstep y hy)
  have hc := hclose (j+1) (M/((2:ℝ)^e.N)^expo) (by positivity) hcap
  have hfac : ((2:ℝ)^e.N)^eps*(e.distanceData a t i X Y).prefixGraphFactor=((2:ℝ)^e.N)^(eps+
      (-2*(e.profile p-e.profile a)+height e.profile a p+(e.C+36*(n+1:ℝ)+5)*sig)) := by
    dsimp [PositiveDistanceState.prefixGraphFactor,RecursiveEnvironmentND.distanceData]
    rw [he,←Real.rpow_add (by positivity : 0<(2:ℝ)^e.N)]
    rfl
  have hexp : eps+(-2*(e.profile p-e.profile a)+height e.profile a p+(e.C+36*(n+1:ℝ)+5)*sig)≤expo := by
    dsimp only [expo,u,DimensionalPolicy.branchExponentND,DimensionalPolicy.branchCost,BranchState.start]
    simp only [show BranchLabel.high ≠ .low by decide,↓reduceIte]
    have hh := mul_le_mul_of_nonneg_right (recursiveLoss_graph n e.C) hsig.le
    linarith only [hh]
  change ((2:ℝ)^e.N)^eps*(e.distanceData a t i X Y).prefixGraphFactor*(e.distanceData a t i X Y).prefixHighChildSup Order (j+1:ℕ) Ψ≤D^(4*total)*M
  change (e.distanceData a t i X Y).prefixHighChildSup Order (j+1:ℕ) Ψ≤D^(4*total)*(M/((2:ℝ)^e.N)^expo) at hc
  rw [hfac]
  have hmul := mul_le_mul_of_nonneg_left hc (by positivity : 0≤((2:ℝ)^e.N)^(eps+
      (-2*(e.profile p-e.profile a)+height e.profile a p+(e.C+36*(n+1:ℝ)+5)*sig)))
  apply hmul.trans
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (power_div_cap hM hexp) (by positivity)

theorem uniform_recursive_prefix_rule (hn : 1≤n)
    {sig K : ℝ} (hsig : 0<sig) (hsig₁ : sig≤1) (hK : 32*(n+2:ℝ)≤K)
    (J : ℕ) (hJ : 0<J) (eps T : ℝ) (heps : 0<eps) (hT : 0<T)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ) (hsupp : tsupport Ψ⊆Ioo (1/4:ℝ) 4)
    (hΨ0 : ∀ r,0≤Ψ r) (hΨ1 : ∀ r∈Icc (1/2:ℝ) 2,1≤Ψ r) (hiΨ : Integrable Ψ) :
    ∃ Order : ℕ,∀ (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
      (B total : ℕ), (∀ L∈W,L.length≤B) → prefixInverseVocabulary n Order⊆W → 2*Order≤total →
    ∃ H E : ℝ,0≤H ∧ 0≤E ∧ ∃ N₀ : ℕ,∀ e : RecursiveEnvironmentND n,
      N₀≤e.N → e.sig=sig → e.J=J →
      ∀ B₀ s,RegularizedProfileData e.ρ e.N B₀ s sig e.mass →
      0<e.q → sig*(e.N:ℝ)≤e.q → ∀ a t i offset, i<e.J → t≤e.N → a+100*e.q<t →
      2*policyDepth e.profile e.N e.q a t≤a+t →
      ∀ M : ℝ,0≤M → ((2:ℝ)^e.N)^(4*(n+2:ℝ)*sig)≤M →
      (∀ u l,DimensionalPolicy.BranchStep e.profile e.N e.q offset sig (.D a t i) l u →
        ∀ x,e.energies K W total Ψ u x →
        ((2:ℝ)^e.N)^(DimensionalPolicy.branchExponentND e.profile (recursiveLoss n e.C) sig sig eps
          (.D a t i) l u)*x≤M) →
      ∀ x,e.energies K W total Ψ (.D a t i) x → x≤H*((e.N:ℝ)+1)*M+E*((2:ℝ)^e.N)^(-T) := by
  obtain ⟨Order,H₀,E,hH₀,hE,N₁,hpref⟩ := uniform_actual_prefix_reduction hn hsig hsig₁ hK J hJ eps T heps hT Ψ hΨ hsupp hΨ0 hΨ1
  refine ⟨Order,?_⟩
  intro W B total hW hV htotal
  obtain ⟨D,hD,N₂,hclose⟩ := uniform_recursive_high_closure W B total Order hW hV htotal hsig
  let H := H₀*(2+2*(32*binKernelConstant.toReal)+2*D^(4*total))
  refine ⟨H,E,by dsimp [H]; positivity,hE,max N₁ N₂,?_⟩
  intro e hN he hJe B₀ s hd hq hslack a t i offset hi ht hw hside M hM hfloor hchildren x hx
  let := hd.probability
  obtain ⟨X,Y,hX,hY,hox,hoy,hsep,rfl⟩ := hx
  let f := e.distanceData a t i X Y
  let p := policyDepth e.profile e.N e.q a t
  have hap : a≤p := (Nat.le_add_right a e.q).trans (policyDepth_interior e.profile hq (policyBlocks_nonempty hq ht hw)).1
  have hb := hpref f (show N₁≤e.N by omega) he hJe hi B₀ s hd hq ht hw hslack hside
    ((mem_dyadicPaths a X).mp hX) ((mem_dyadicPaths a Y).mp hY) hox hoy hsep
  have hloeach (j : ℕ) (hj : j∈f.prefixLowIndices) :
      ({f with t:=j+1,i:=f.i+1} : PositiveDistanceState (n+1)).coincidence.toReal≤M := by
    obtain ⟨hj,hgap⟩ := Finset.mem_filter.mp hj
    have hj := Finset.mem_Ico.mp hj
    have hstep : DimensionalPolicy.BranchStep e.profile e.N e.q offset sig (.D a t i) .low (.D a (j+1) (i+1)) :=
      .low hw (Finset.mem_Ioc.mpr (by dsimp [f,RecursiveEnvironmentND.distanceData] at hj; omega)) (by simpa only [f,RecursiveEnvironmentND.distanceData,he] using hgap)
    have hh := hchildren _ _ hstep _ (e.distance_mem K W total Ψ a (j+1) (i+1) X Y hX hY hox hoy hsep)
    have hexp : 0≤DimensionalPolicy.branchExponentND e.profile (recursiveLoss n e.C) sig sig eps (.D a t i) .low (.D a (j+1) (i+1)) := by
      simpa [DimensionalPolicy.branchExponentND,DimensionalPolicy.branchCost,BranchState.start] using heps.le
    have hh' := weighted_child_cap ENNReal.toReal_nonneg hexp hh
    simpa only [Real.rpow_zero,one_mul,f,RecursiveEnvironmentND.distanceData] using hh'
  have hlocard : f.prefixLowIndices.card≤e.N := by
    exact (Finset.card_filter_le _ _).trans (by simpa only [Nat.card_Ico] using (Nat.sub_le f.t f.a).trans ht)
  have hlo : (∑ j∈f.prefixLowIndices,({f with t:=j+1,i:=f.i+1} : PositiveDistanceState (n+1)).coincidence.toReal)≤(e.N:ℝ)*M := by
    calc
      _≤∑ j∈f.prefixLowIndices,M := Finset.sum_le_sum hloeach
      _=(f.prefixLowIndices.card:ℝ)*M := by simp
      _≤(e.N:ℝ)*M := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hlocard) hM
  have hhieach (j : ℕ) (hj : j∈f.prefixHighIndices) :
      ((2:ℝ)^e.N)^eps*f.prefixGraphFactor*f.prefixHighChildSup Order (j+1:ℕ) Ψ≤D^(4*total)*M := by
    apply prefix_high_weighted_cap hsig e he a t i offset Order total W X Y K eps D M hD hM Ψ hiΨ hΨ0 hq ht hw hside hchildren
    · intro v M' hM' hcap
      exact hclose f (show N₂≤e.N by omega) he (show IsFiniteMeasure e.ρ from inferInstance) hq hap v Ψ (hiΨ.comp_div (by positivity)) hΨ0 K M' hM' hcap
    · exact hj
  have hhi : ((2:ℝ)^e.N)^eps*f.prefixGraphFactor*(∑ j∈f.prefixHighIndices,f.prefixHighChildSup Order (j+1:ℕ) Ψ)≤D^(4*total)*(e.N:ℝ)*M := by
    rw [Finset.mul_sum]
    calc
      _≤∑ j∈f.prefixHighIndices,D^(4*total)*M := Finset.sum_le_sum hhieach
      _=(f.prefixHighIndices.card:ℝ)*(D^(4*total)*M) := by simp
      _≤(e.N:ℝ)*(D^(4*total)*M) := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (f.prefixHighIndices_card_bound ht)) (by positivity)
      _=_ := by ring
  have hmain : H₀*(2*((2:ℝ)^e.N)^(4*(n+2:ℝ)*sig)+2*(32*binKernelConstant.toReal)*
      (∑ j∈f.prefixLowIndices,({f with t:=j+1,i:=f.i+1} : PositiveDistanceState (n+1)).coincidence.toReal)+
      2*((2:ℝ)^e.N)^eps*f.prefixGraphFactor*(∑ j∈f.prefixHighIndices,f.prefixHighChildSup Order (j+1:ℕ) Ψ))≤H*((e.N:ℝ)+1)*M := by
    have h₁ := mul_le_mul_of_nonneg_left hfloor (by positivity : 0≤2*H₀)
    have h₂ := mul_le_mul_of_nonneg_left hlo (by positivity : 0≤H₀*(2*(32*binKernelConstant.toReal)))
    have h₃ := mul_le_mul_of_nonneg_left hhi (by positivity : 0≤2*H₀)
    have h₄ : 0≤2*H₀*(e.N:ℝ)*M+H₀*(2*(32*binKernelConstant.toReal))*M+2*H₀*D^(4*total)*M := by positivity
    dsimp [H]
    nlinarith only [h₁,h₂,h₃,h₄]
  exact hb.trans (add_le_add hmain le_rfl)
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
theorem uniform_recursive_direct_rule {sig : ℝ} (hsig : 0<sig)
    (T : ℝ) (J : ℕ) (hJ : 0<J) (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ)
    (hsupp : tsupport Ψ⊆Ioo (1/4:ℝ) 4) (hΨ0 : ∀ r,0≤Ψ r) (hiΨ : Integrable Ψ)
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (B total : ℕ) (hW : ∀ L∈W,L.length≤B) :
    ∃ H E : ℝ,1≤H ∧ 0≤E ∧ ∃ N₀ : ℕ,∀ e : RecursiveEnvironmentND n,
      N₀≤e.N → e.sig=sig → e.J=J →
      ∀ B₀ s,RegularizedProfileData e.ρ e.N B₀ s sig e.mass →
      0<e.q → ⌈10*sig*(e.N:ℝ)⌉₊<e.q → sig*(e.N:ℝ)≤e.q → 10*sig*(e.N:ℝ)≤e.q →
      ∀ a₀ t₀ a v i offset, i<e.J → (BranchState.H a₀ t₀ a v i).Valid e.N sig → a+100*e.q<v →
      (BranchState.H a₀ t₀ a v i).nearDepth e.profile e.N e.q sig≤a →
      ∀ K eps M : ℝ,0≤eps → 0≤M →
      (∀ u l,DimensionalPolicy.BranchStep e.profile e.N e.q offset sig (.H a₀ t₀ a v i) l u →
        ∀ x,e.energies K W total Ψ u x →
        ((2:ℝ)^e.N)^(DimensionalPolicy.branchExponentND e.profile (recursiveLoss n e.C) sig sig eps
          (.H a₀ t₀ a v i) l u)*x≤M) →
      ∀ x,e.energies K W total Ψ (.H a₀ t₀ a v i) x → x≤H*M+E*((2:ℝ)^e.N)^(-T) := by
  obtain ⟨j,hgraph⟩ := uniform_recursive_direct_graph (n:=n) hsig T J hJ Ψ hΨ hsupp hΨ0
  obtain ⟨E,hE,N₁,hgraph⟩ := hgraph W B total hW 1 (by norm_num)
  obtain ⟨D,hD,hrem⟩ := uniform_recursive_reached_removal W B total hW hsig 1 (by norm_num)
  obtain ⟨N₂,hrem⟩ := eventually_atTop.mp hrem
  refine ⟨D^(4*total),E,one_le_pow₀ hD,hE,max N₁ N₂,?_⟩
  intro e hN he hJe B₀ s hd hq hceil hslack hslack10 a₀ t₀ a v i offset hi hv hw hdir K eps M heps hM hchildren x hx
  let := hd.probability
  obtain ⟨X,Y,hX,hY,hox,hoy,L₁,L₂,f,g,hf,hg,hfn,hgn,hw₁,hw₂,ht₁,ht₂,rfl⟩ := hx
  let r := e.angularData a₀ t₀ a v i X Y
  obtain ⟨b,hb,hgraph⟩ := hgraph r (show N₁≤e.N by omega) he hJe hi B₀ s hd hq hceil hslack hslack10
    hv.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2 hw hdir hX hY hox hoy
    L₁ L₂ f g recursiveUnit recursiveUnit hf hg hfn hgn hw₁ hw₂ ht₁ ht₂
    (fun l _ w _ => recursiveUnit_jets l w) (fun l _ w _ => recursiveUnit_jets l w)
  let p := descriptorAnchor b
  let exponent := DimensionalPolicy.branchExponentND e.profile (recursiveLoss n e.C) sig sig eps
    (.H a₀ t₀ a v i) .direct (.H a₀ t₀ p v i)
  have hstep : DimensionalPolicy.BranchStep e.profile e.N e.q offset sig
      (.H a₀ t₀ a v i) .direct (.H a₀ t₀ p v i) := .direct hw hb
  have hRp : 0<((2:ℝ)^e.N)^exponent := by positivity
  have hcap : r.reachedChildren p L₁ L₂ f g recursiveUnit recursiveUnit Ψ≤M/((2:ℝ)^e.N)^exponent := by
    apply r.reachedChildren_le _ _ _ _ _ _ _ _ _ (by positivity)
    intro U V hU hV hou hov
    have hh := hchildren _ _ hstep _ (r.successor_energy_mem K W total Ψ p U V hU hV hou hov
      L₁ L₂ f g hf hg hfn hgn hw₁ hw₂ ht₁ ht₂)
    exact (le_div_iff₀ hRp).mpr (by simpa only [mul_comm] using hh)
  have hr := hrem e.N (by omega) r rfl he (show IsFiniteMeasure e.ρ from inferInstance) hq p hb.anchor_gt.le
    L₁ L₂ f g recursiveUnit recursiveUnit hf hg hfn hgn hw₁ hw₂ ht₁ ht₂
    (fun _ _ => by norm_num [recursiveUnit]) (fun _ _ => by norm_num [recursiveUnit])
    Ψ (hiΨ.comp_div (by positivity)) hΨ0
  have hr' := hr.trans (mul_le_mul_of_nonneg_left hcap (by positivity : 0≤D^(4*total)))
  have heq : r.graphFactor p=((2:ℝ)^e.N)^(-2*(e.profile p-e.profile a)+height e.profile a p+
      (e.C+36*(n+1:ℝ)+5)*sig) := by simp only [RecursiveAngularND.graphFactor,r,RecursiveEnvironmentND.angularData,he]; rfl
  have hexp : -2*(e.profile p-e.profile a)+height e.profile a p+(e.C+36*(n+1:ℝ)+5)*sig≤exponent := by
    unfold exponent DimensionalPolicy.branchExponentND DimensionalPolicy.branchCost
    simp only [BranchState.start,show BranchLabel.direct ≠ .low by decide,↓reduceIte]
    have hh := mul_le_mul_of_nonneg_right (recursiveLoss_graph n e.C) hsig.le
    nlinarith
  have hpay : r.graphFactor p*(M/((2:ℝ)^e.N)^exponent)≤M := by
    rw [heq]; exact power_div_cap hM hexp
  have hgain : r.graphFactor p*r.sameSymbolChildren p L₁ L₂ f g recursiveUnit recursiveUnit Ψ≤D^(4*total)*M := by
    calc
      _≤r.graphFactor p*(D^(4*total)*(M/((2:ℝ)^e.N)^exponent)) := mul_le_mul_of_nonneg_left hr' (by rw [heq]; positivity)
      _=D^(4*total)*(r.graphFactor p*(M/((2:ℝ)^e.N)^exponent)) := by ring
      _≤D^(4*total)*M := mul_le_mul_of_nonneg_left hpay (by positivity)
  exact hgraph.trans (add_le_add hgain le_rfl)
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
theorem uniform_recursive_near_far_rule
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ) (hsupp : tsupport Ψ⊆Ioo (1/4:ℝ) 4)
    (hΨ0 : ∀ r,0≤Ψ r) {sig : ℝ} (hsig : 0<sig) (hsig₁ : sig≤1)
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (B total : ℕ) (hW : ∀ L∈W,L.length≤B) {J : ℕ} (hJ : 0<J)
    (T : ℝ) (ell : ℕ) (hK : 32*(n+2:ℝ)≤(2:ℝ)^ell) :
    ∃ H : ℝ,0≤H ∧ ∃ N₀ : ℕ,∀ e : RecursiveEnvironmentND n,
      N₀≤e.N → e.sig=sig → e.J=J →
      ∀ B₀ s,RegularizedProfileData e.ρ e.N B₀ s sig e.mass → 0<e.q →
      ∀ a₀ t₀ a v i,(BranchState.H a₀ t₀ a v i).Valid e.N sig → a+100*e.q<v →
      a<(BranchState.H a₀ t₀ a v i).nearDepth e.profile e.N e.q sig →
      ∀ eps M : ℝ,0≤eps → 0≤M →
      (∀ u l,DimensionalPolicy.BranchStep e.profile e.N e.q (ell+2) sig (.H a₀ t₀ a v i) l u →
        ∀ x,e.energies ((2:ℝ)^ell) W total Ψ u x →
        ((2:ℝ)^e.N)^(DimensionalPolicy.branchExponentND e.profile (recursiveLoss n e.C) sig sig eps
          (.H a₀ t₀ a v i) l u)*x≤M) →
      ∀ x,e.energies ((2:ℝ)^ell) W total Ψ (.H a₀ t₀ a v i) x →
        x≤H*((e.N:ℝ)+1)*M+((2:ℝ)^e.N)^(-T) := by
  obtain ⟨j,D,H,hD,hH,N₁,hnf⟩ := uniform_recursive_near_far hΨ hsupp hΨ0 hsig hsig₁ W B total hW hJ
    1 (by norm_num) T (ell+2:ℝ) ell hK
  obtain ⟨N₂,hbuffer⟩ := DimensionalPolicy.uniform_far_offset_buffer hsig (ell+2)
  let Cnear := (20*(n+2:ℝ)+5)^(2*(n+1))*D^(4*total)
  refine ⟨Cnear+H,by dsimp only [Cnear]; positivity,max N₁ N₂,?_⟩
  intro e hN he hJe B₀ s hd hq a₀ t₀ a v i hv hw hnear eps M heps hM hchildren x hx
  let := hd.probability
  obtain ⟨X,Y,hX,hY,hox,hoy,L₁,L₂,f,g,hf,hg,hfn,hgn,hw₁,hw₂,ht₁,ht₂,rfl⟩ := hx
  let r := e.angularData a₀ t₀ a v i X Y
  let h := (BranchState.H a₀ t₀ a v i).nearDepth e.profile e.N e.q sig
  let expn := DimensionalPolicy.branchExponentND e.profile (recursiveLoss n e.C) sig sig eps
    (.H a₀ t₀ a v i) .near (.H a₀ t₀ h v i)
  let expf := fun b => DimensionalPolicy.branchExponentND e.profile (recursiveLoss n e.C) sig sig eps
    (.H a₀ t₀ a v i) .far (.D b v (i+1))
  have hhv : h+ell+2<v := by
    have hh := hbuffer e.N (by omega) ((BranchState.H a₀ t₀ a v i).descriptors e.profile e.N e.q |>.sup descriptorLength) v a hnear
    simpa only [h,BranchState.nearDepth,BranchState.finish,Nat.add_assoc] using hh
  have hhN : h+ell+2≤e.N := (Nat.le_of_lt hhv).trans (hv.2.2.1.trans hv.2.2.2.1)
  have hdepth : ((h+ell+2:ℕ):ℝ)≤(v:ℝ)-2*(max ((r.retainedList a).sup descriptorLength) (Nat.ceil (10*sig*e.N)):ℕ)+(ell+2:ℝ) := by
    let b := sourceFarBuffer e.N (((BranchState.H a₀ t₀ a v i).descriptors e.profile e.N e.q).sup descriptorLength) sig
    have hh : h=v-2*b := rfl
    have hvb : 2*b≤v := by dsimp only [h] at hh; omega
    have hh' : (h:ℝ)=(v:ℝ)-2*(b:ℝ) := by rw [hh,Nat.cast_sub hvb]; push_cast; rfl
    change ((h+ell+2:ℕ):ℝ)≤(v:ℝ)-2*(b:ℝ)+(ell+2:ℝ)
    push_cast
    linarith
  have hncap (U V : CellPath (n+1)) (hU : U∈dyadicPaths h) (hV : V∈dyadicPaths h)
      (hou : 0<e.ρ (treeCell U)) (hov : 0<e.ρ (treeCell V)) :
      (r.successor h U V).energy L₁ L₂ f g recursiveUnit recursiveUnit Ψ≤M/((2:ℝ)^e.N)^expn := by
    have hh := hchildren _ _ (.near hw hnear) _ (r.successor_energy_mem ((2:ℝ)^ell) W total Ψ h U V hU hV hou hov
      L₁ L₂ f g hf hg hfn hgn hw₁ hw₂ ht₁ ht₂)
    exact (le_div_iff₀ (by positivity : 0<((2:ℝ)^e.N)^expn)).mpr (by simpa only [mul_comm] using hh)
  have hfcap (b : ℕ) (hb : b∈Finset.Icc (a+1) (h+ell+2)) (U V : CellPath (n+1))
      (hU : U∈dyadicPaths b) (hV : V∈dyadicPaths b) (hou : 0<e.ρ (treeCell U)) (hov : 0<e.ρ (treeCell V))
      (hs : Attempt4FullFar.farSeparatedGridND b ((2:ℝ)^ell) (fun j => (pathIndex U j:ℤ)) (fun j => (pathIndex V j:ℤ))) :
      (e.distanceData b v (i+1) U V).coincidence.toReal≤M/((2:ℝ)^e.N)^(expf b) := by
    have hh := hchildren _ _ (.far hw hnear (by simpa only [Nat.add_assoc] using hb)) _
      (e.distance_mem ((2:ℝ)^ell) W total Ψ b v (i+1) U V hU hV hou hov hs)
    exact (le_div_iff₀ (by positivity : 0<((2:ℝ)^e.N)^(expf b))).mpr (by simpa only [mul_comm] using hh)
  have hb := hnf r (show N₁≤e.N by omega) he hJe B₀ s hd hq hv.2.2.2.1 hv.1 hv.2.2.1
    h hnear hhN hdepth hX hY hox hoy L₁ L₂ f g recursiveUnit recursiveUnit
    (M/((2:ℝ)^e.N)^expn) (fun b => M/((2:ℝ)^e.N)^(expf b)) hf hg hfn hgn hw₁ hw₂ ht₁ ht₂
    (fun l _ w _ => recursiveUnit_jets l w) (fun l _ w _ => recursiveUnit_jets l w)
    hncap (fun _ _ => by positivity) hfcap
  have hdim := mul_le_mul_of_nonneg_right (recursiveLoss_dim n e.C) hsig.le
  have hnexp : -2*(e.profile h-e.profile a)+4*(n+2:ℝ)*sig≤expn := by
    dsimp only [expn,DimensionalPolicy.branchExponentND,DimensionalPolicy.branchCost,BranchState.start]
    simp only [show BranchLabel.near ≠ .low by decide,↓reduceIte]
    nlinarith
  have hfexp (b : ℕ) : -2*(e.profile b-e.profile a)+4*(n+2:ℝ)*sig≤expf b := by
    dsimp only [expf,DimensionalPolicy.branchExponentND,DimensionalPolicy.branchCost,BranchState.start]
    simp only [show BranchLabel.far ≠ .low by decide,↓reduceIte]
    nlinarith
  have hnpay := power_div_cap (N:=e.N) hM hnexp
  have hfpay : (∑ b∈Finset.Icc (a+1) (h+ell+2),((2:ℝ)^e.N)^(-2*(e.profile b-e.profile a)+4*(n+2:ℝ)*sig)*
      (M/((2:ℝ)^e.N)^(expf b)))≤(e.N:ℝ)*M := by
    calc
      _≤∑ b∈Finset.Icc (a+1) (h+ell+2),M := Finset.sum_le_sum (fun b _ => power_div_cap hM (hfexp b))
      _=((Finset.Icc (a+1) (h+ell+2)).card:ℝ)*M := by simp
      _≤(e.N:ℝ)*M := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by rw [Nat.card_Icc]; omega)) hM
  have hbound : Cnear*(((2:ℝ)^e.N)^(-2*(e.profile h-e.profile a)+4*(n+2:ℝ)*sig)*(M/((2:ℝ)^e.N)^expn))+
      H*(∑ b∈Finset.Icc (a+1) (h+ell+2),((2:ℝ)^e.N)^(-2*(e.profile b-e.profile a)+4*(n+2:ℝ)*sig)*(M/((2:ℝ)^e.N)^(expf b)))≤
      (Cnear+H)*((e.N:ℝ)+1)*M := by
    have hh₁ := mul_le_mul_of_nonneg_left hnpay (by dsimp only [Cnear]; positivity : 0≤Cnear)
    have hh₂ := mul_le_mul_of_nonneg_left hfpay hH
    have hh₃ : 0≤Cnear*(e.N:ℝ)*M+H*M := by dsimp only [Cnear]; positivity
    nlinarith only [hh₁,hh₂,hh₃]
  have hb' : (e.angularData a₀ t₀ a v i X Y).energy L₁ L₂ f g recursiveUnit recursiveUnit Ψ ≤
      Cnear*(((2:ℝ)^e.N)^(-2*(e.profile h-e.profile a)+4*(n+2:ℝ)*sig)*(M/((2:ℝ)^e.N)^expn))+
      H*(∑ b∈Finset.Icc (a+1) (h+ell+2),((2:ℝ)^e.N)^(-2*(e.profile b-e.profile a)+4*(n+2:ℝ)*sig)*(M/((2:ℝ)^e.N)^(expf b)))+
      ((2:ℝ)^e.N)^(-T) := by
    simpa only [r,RecursiveEnvironmentND.angularData,RecursiveAngularND.profile,Cnear,mul_assoc] using hb
  exact hb'.trans (add_le_add hbound le_rfl)
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
