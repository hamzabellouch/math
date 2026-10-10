import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Recursion.PrefixShellLeSourceShellSuccessor
import OAI.MeasureTheory.FalconerCompletion.Shells.PrefixParallelMem
import OAI.MeasureTheory.FalconerCompletion.Shells.PrefixPhasedGlobalBound
import OAI.MeasureTheory.FalconerCompletion.Shells.PrefixShell
import OAI.MeasureTheory.FalconerCompletion.Shells.ShellEffectiveScale2

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer GraphLiteralSupport.Attempt4FullFar
open scoped ContDiff
variable {n : ℕ}

theorem actual_prefix_high_shell (hn : 1 ≤ n)
    {sig K : ℝ} (hsig : 0 < sig) (hsig₁ : sig ≤ 1) (hK : 32*(n+2:ℝ) ≤ K)
    (Jsmooth : ℕ) (hJ : 0 < Jsmooth) (ε T : ℝ) (hε : 0 < ε) (hT : 0 < T)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ) (hsupp : tsupport Ψ ⊆ Ioo (1/4:ℝ) 4)
    (hΨ0 : ∀ r, 0 ≤ Ψ r) (hΨ1 : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r) :
    ∃ Order : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ (e : PositiveDistanceState (n+1)),
    N₀ ≤ e.N → e.sig=sig → e.J=Jsmooth → e.i < e.J →
    ∀ (B : ℕ) (s : ℝ), RegularizedProfileData e.ρ e.N B s sig e.mass →
    0 < e.q → e.t ≤ e.N → e.a+100*e.q < e.t → sig*e.N ≤ e.q →
    2*e.sourcePrefixDepth ≤ e.a+e.t →
    e.X.length=e.a → e.Y.length=e.a → 0 < e.ρ (treeCell e.X) → 0 < e.ρ (treeCell e.Y) →
    farSeparatedGridND e.a K (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ)) →
    ∀ v : ℕ, v+1 ≤ e.t → (e.t:ℝ)-(v+1:ℕ) < sig*e.N →
      e.prefixShell v ≤ ((2:ℝ)^e.N)^ε*e.prefixGraphFactor*e.prefixHighChildSup Order (v+1) Ψ +
        C*((2:ℝ)^e.N)^(-T) := by
  classical
  have hKpos : 0 < K := by have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  choose D hD hderiv using (fun m : ℕ => uniform_prefixEndpoint_derivatives (n:=n) m)
  have hsource (Z : Fin (n+1) → ℤ) :=
    Attempt4PrefixShell.source_weighted_shellND (ι:=PolicyDescriptor) (κ:=PolicyDescriptor)
      (separatedCutoff 0 Z 0) (separatedCutoff_contDiff _ _ _) 3 D sig ε T
      (2*(n+2:ℝ)*sig) 16 1 (8*K) hsig hsig₁ hD hε (by norm_num) (by positivity)
  choose order hsource using hsource
  let offsets := (separatedOffsets_finite (d:=n+1) K).toFinset
  let Order := offsets.sup order
  have hξ := (Filter.eventually_all_finite (separatedOffsets_finite (d:=n+1) K)).mpr
    (fun Z _ => hsource Z)
  obtain ⟨N₁,hsource⟩ := Filter.eventually_atTop.mp hξ
  obtain ⟨Cg,hCg,N₂,hgraph⟩ := uniform_actual_prefix_inverse_graph hn hsig hK Jsmooth Order hJ
    (T+ε) (by linarith) Ψ hΨ hsupp hΨ0 hΨ1
  refine ⟨Order,Cg+1,by positivity,max 1 (max N₁ N₂),?_⟩
  intro e hN hse hJe hi B s hρ hq htN hwide hqscale hpref hX hY hoccX hoccY hsep v hv hhigh
  have hN1 : 1 ≤ e.N := (le_max_left _ _).trans hN
  have hN₁ : N₁ ≤ e.N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN₂ : N₂ ≤ e.N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  let := hρ.probability
  let := e.weightedDistance_isFinite hK hX hY hsep
  have haN : e.a ≤ e.N := by omega
  have hcompact : HasCompactSupport Ψ :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport Ψ) (hsupp.trans Ioo_subset_Icc_self)
  have hiΨ : Integrable (fun r => Ψ (r/(2:ℝ)^(v+1:ℕ))) :=
    (hΨ.continuous.integrable_of_hasCompactSupport hcompact).comp_div (by positivity)
  have hiΨ' : Integrable (fun r => Ψ (r/(2:ℝ)^((v+1:ℕ):ℝ))) := by
    simpa only [Real.rpow_natCast] using hiΨ
  have hsup := e.prefixHighChildSup_nonneg Order (v+1:ℕ) Ψ hiΨ' hΨ0
  have hfactor : 0 ≤ e.prefixGraphFactor := by unfold PositiveDistanceState.prefixGraphFactor; positivity
  let BHF := e.prefixGraphFactor*e.prefixHighChildSup Order (v+1:ℕ) Ψ+
    Cg*((2:ℝ)^e.N)^(-(T+ε))
  have hBHF : 0 ≤ BHF := add_nonneg (mul_nonneg hfactor hsup) (by positivity)
  have hHF : ∀ j ≤ Order, ∀ z ∈ Attempt4PrefixShell.inverseAngularTermsND j
      (e.prefixDescriptors.disjSum e.prefixDescriptors), ∀ ξ, e.prefixAngularHF (v+1:ℕ) Ψ z ξ ≤ BHF := by
    intro j hj z hz ξ
    apply (hgraph e hN₂ hse hJe hi B s hρ hq htN hwide hqscale hpref hX hY hoccX hoccY hsep
      (v+1:ℕ) (by exact_mod_cast hv) hhigh j hj z hz ξ).trans
    exact add_le_add (mul_le_mul_of_nonneg_left
      (e.prefixGraphChildMax_le_sup Order (v+1:ℕ) Ψ hiΨ' hΨ0 hj hz ξ) hfactor) le_rfl
  let Z : Fin (n+1) → ℤ := (fun j => (pathIndex e.X j:ℤ))-(fun j => (pathIndex e.Y j:ℤ))
  have hZ : Z∈separatedOffsets K := gridOffset_mem hsep
  have horder : order Z ≤ Order := Finset.le_sup (f:=order)
    ((separatedOffsets_finite (d:=n+1) K).mem_toFinset.mpr hZ)
  have hcutEq : separatedCutoff 0 Z 0=e.prefixCutoff := (separatedCutoff_offset e.a _ _).symm
  have hh := hsource e.N hN₁ Z hZ
  dsimp only at hh
  rw [hcutEq,←hse] at hh
  have hreg := e.prefixHigh_shell_regime hsig htN hwide hqscale hv hhigh
  have hgeometry : ∀ x∈treeCell e.X, ∀ y∈treeCell e.Y,
      1 ≤ dist x y*(2:ℝ)^(e.a:ℝ) ∧ dist x y*(2:ℝ)^(e.a:ℝ) ≤ 8*K := by
    intro x hx y hy
    simpa only [Real.rpow_natCast] using e.separated_distance_ratio hK hX hY hsep (z:=(x,y)) hx hy
  choose G hG hsbound using (fun z : PrefixAssignment n => e.prefixInverse_global_bound z)
  have hshell := hh e.prefixDescriptors e.prefixDescriptors e.prefixEndpointSmooth e.prefixEndpointSmooth
    (fun _ => 1) (fun _ => 1)
    (fun b => sourceMaskScaleND (descriptorLength b) ((2:ℝ)^e.N) e.sig)
    (fun b => sourceMaskScaleND (descriptorLength b) ((2:ℝ)^e.N) e.sig)
    (e.prefixDescriptors_card_max hN1 hq) e.ρ e.ρ (treeCell e.X) (treeCell e.Y)
    (measurableSet_treeCell _) (measurableSet_treeCell _) ((e.t-e.a)/2)
    e.levelMass e.levelMass e.a (v+1:ℕ)
    (by simpa only [hse] using hreg.1) (by simpa only [hse] using hreg.2.1) hreg.2.2
    (by simpa only [hse] using e.prefixShell_normalized_mass hρ haN hX hY)
    (fun b hb => e.prefixDescriptor_scale hq hb) (fun b hb => e.prefixDescriptor_scale hq hb)
    (fun x _ b _ w hw => e.prefixEndpoint_norm_le x w b hw)
    (fun y _ b _ w hw => e.prefixEndpoint_norm_le y w b hw)
    (fun x _ b _ j hj w _ => hderiv _ e x b j hj w)
    (fun y _ b _ j hj w _ => hderiv _ e y b j hj w)
    hgeometry (e.ae_prefixCutoff_local (by convert hK using 1; push_cast; ring) hX hY hsep)
    (Filter.Eventually.of_forall (fun _ => by simp))
    (by simpa only [map_one,one_mul,e.prefix_pairMask_radial,Function.comp_def] using
      Complex.continuous_ofReal.measurable.comp e.measurable_minimalMask)
    1 e.prefixCutoff_norm_le (fun _ => G) (fun _ => G)
    (fun _ _ z _ => e.prefixInverseLeft_measurable z)
    (fun _ _ z _ => e.prefixInverseRight_measurable z)
    (fun _ _ z _ x w => (hsbound z x w).1) (fun _ _ z _ y w => (hsbound z y w).2)
    Ψ hiΨ' hΨ0 hΨ1 BHF hBHF
    (fun j hj z hz ξ => by
      simp only [Real.rpow_natCast]
      exact hHF j (hj.trans horder) z hz ξ)
  have hmain := (e.prefixShell_le_sourceShell_successor v).trans
    (by simpa only [Real.rpow_natCast] using hshell.2)
  apply hmain.trans_eq
  have hpay : ((2:ℝ)^e.N)^ε*((2:ℝ)^e.N)^(-(T+ε))=((2:ℝ)^e.N)^(-T) := by
    rw [←Real.rpow_add (by positivity : 0 < (2:ℝ)^e.N)]
    congr 1
    ring
  dsimp only [BHF]
  calc
    _ = ((2:ℝ)^e.N)^ε*e.prefixGraphFactor*e.prefixHighChildSup Order (v+1:ℕ) Ψ+
      Cg*(((2:ℝ)^e.N)^ε*((2:ℝ)^e.N)^(-(T+ε)))+((2:ℝ)^e.N)^(-T) := by ring
    _ = _ := by rw [hpay]; simp only [Nat.cast_add,Nat.cast_one]; ring
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND.PositiveDistanceState
open Set MeasureTheory
variable {d : ℕ} (e : PositiveDistanceState d)
lemma prefixHighIndices_spec {j : ℕ} (hj : j ∈ e.prefixHighIndices) :
    j+1 ≤ e.t ∧ (e.t:ℝ)-(j+1:ℕ) < e.sig*e.N := by
  have hj' := Finset.mem_filter.mp hj
  exact ⟨Nat.succ_le_of_lt (Finset.mem_Ico.mp hj'.1).2, lt_of_not_ge hj'.2⟩

lemma prefixHighIndices_card_bound (htN : e.t ≤ e.N) : e.prefixHighIndices.card ≤ e.N := by
  calc
    _ ≤ (Finset.Ico e.a e.t).card := Finset.card_filter_le _ _
    _ = e.t-e.a := Nat.card_Ico _ _
    _ ≤ e.N := (Nat.sub_le _ _).trans htN

lemma prefixHigh_sum_bound (A C : ℝ) (H : ℕ → ℝ)
    (h : ∀ j ∈ e.prefixHighIndices, e.prefixShell j ≤ A*H j+C) :
    (∑ j∈e.prefixHighIndices, e.prefixShell j) ≤
      A*(∑ j∈e.prefixHighIndices, H j)+(e.prefixHighIndices.card:ℝ)*C := by
  calc
    _ ≤ ∑ j∈e.prefixHighIndices, (A*H j+C) := Finset.sum_le_sum h
    _ = _ := by rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_const]; simp only [nsmul_eq_mul]

lemma prefixHigh_error_absorption (htN : e.t ≤ e.N) (Cs T : ℝ) (hCs : 0 ≤ Cs) :
    (e.prefixHighIndices.card:ℝ)*(Cs*((2:ℝ)^e.N)^(-(T+1))) ≤ Cs*((2:ℝ)^e.N)^(-T) := by
  have hNR : (e.N:ℝ) ≤ (2:ℝ)^e.N := by
    exact_mod_cast Nat.le_of_lt ((Nat.lt_two_pow_self (n:=e.N)))
  have hpay : (2:ℝ)^e.N*((2:ℝ)^e.N)^(-(T+1))=((2:ℝ)^e.N)^(-T) := by
    conv_lhs => left; rw [←Real.rpow_one ((2:ℝ)^e.N)]
    rw [←Real.rpow_add (by positivity : 0 < (2:ℝ)^e.N)]
    congr 1
    ring
  have hcard : (e.prefixHighIndices.card:ℝ) ≤ e.N := by exact_mod_cast e.prefixHighIndices_card_bound htN
  calc
    _ ≤ (2:ℝ)^e.N*(Cs*((2:ℝ)^e.N)^(-(T+1))) :=
      mul_le_mul_of_nonneg_right (hcard.trans hNR) (by positivity)
    _ = Cs*((2:ℝ)^e.N*((2:ℝ)^e.N)^(-(T+1))) := by ring
    _ = _ := by rw [hpay]
end GraphLiteralSupport.CurrentFalconer.TreeND.PositiveDistanceState
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
lemma prefix_high_accumulation {D H S L X W₁ W₂ Q Cs E : ℝ} (hH : 0 ≤ H)
    (hd : D ≤ H*(S+L+2*X)) (hx : X ≤ W₁*W₂*Q+Cs*E) :
    D ≤ H*(S+L+2*W₁*W₂*Q)+(2*H*Cs)*E := by
  have h := mul_le_mul_of_nonneg_left hx (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hH)
  nlinarith only [hd,h]
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer GraphLiteralSupport.Attempt4FullFar
open scoped ContDiff
variable {n : ℕ}

theorem uniform_actual_prefix_reduction (hn : 1 ≤ n)
    {sig K : ℝ} (hsig : 0 < sig) (hsig₁ : sig ≤ 1) (hK : 32*(n+2:ℝ) ≤ K)
    (Jsmooth : ℕ) (hJ : 0 < Jsmooth) (ε T : ℝ) (hε : 0 < ε) (hT : 0 < T)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ) (hsupp : tsupport Ψ ⊆ Ioo (1/4:ℝ) 4)
    (hΨ0 : ∀ r, 0 ≤ Ψ r) (hΨ1 : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r) :
    ∃ Order : ℕ, ∃ H C : ℝ, 0 < H ∧ 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ (e : PositiveDistanceState (n+1)),
    N₀ ≤ e.N → e.sig=sig → e.J=Jsmooth → e.i < e.J →
    ∀ (B : ℕ) (s : ℝ), RegularizedProfileData e.ρ e.N B s sig e.mass →
    0 < e.q → e.t ≤ e.N → e.a+100*e.q < e.t → sig*e.N ≤ e.q →
    2*e.sourcePrefixDepth ≤ e.a+e.t →
    e.X.length=e.a → e.Y.length=e.a → 0 < e.ρ (treeCell e.X) → 0 < e.ρ (treeCell e.Y) →
    farSeparatedGridND e.a K (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ)) →
    e.coincidence.toReal ≤ H*(2*((2:ℝ)^e.N)^(4*(n+2:ℝ)*sig)+
      2*(32*binKernelConstant.toReal)*
        (∑ j∈e.prefixLowIndices, ({e with t:=j+1,i:=e.i+1} : PositiveDistanceState (n+1)).coincidence.toReal)+
      2*((2:ℝ)^e.N)^ε*e.prefixGraphFactor*
        (∑ j∈e.prefixHighIndices, e.prefixHighChildSup Order (j+1:ℕ) Ψ))+
      C*((2:ℝ)^e.N)^(-T) := by
  classical
  obtain ⟨H,hH,N₁,hdecomp⟩ := uniform_actual_prefix_decomposition (n:=n) hsig hJ hK
  obtain ⟨Order,Cs,hCs,N₂,hshell⟩ := actual_prefix_high_shell hn hsig hsig₁ hK
    Jsmooth hJ ε (T+1) hε (by linarith) Ψ hΨ hsupp hΨ0 hΨ1
  refine ⟨Order,H,2*H*Cs,hH,by positivity,max N₁ N₂,?_⟩
  intro e hN hse hJe hi B s hρ hq htN hwide hqscale hpref hX hY hoccX hoccY hsep
  have hN₁ : N₁ ≤ e.N := (le_max_left _ _).trans hN
  have hN₂ : N₂ ≤ e.N := (le_max_right _ _).trans hN
  have hat : e.a ≤ e.t := by omega
  have hd := hdecomp e hN₁ hse hJe hq hat htN hX hY hsep B s sig hρ
  have hsum := e.prefixHigh_sum_bound (((2:ℝ)^e.N)^ε*e.prefixGraphFactor)
    (Cs*((2:ℝ)^e.N)^(-(T+1))) (fun j => e.prefixHighChildSup Order (j+1:ℕ) Ψ) (by
      intro j hj
      have hj' := e.prefixHighIndices_spec hj
      simpa only [Nat.cast_add,Nat.cast_one] using hshell e hN₂ hse hJe hi B s hρ hq htN hwide hqscale hpref
        hX hY hoccX hoccY hsep j hj'.1 (by simpa only [hse] using hj'.2))
  have herr := e.prefixHigh_error_absorption htN Cs T hCs
  have hsum' := hsum.trans (add_le_add_right herr _)
  exact prefix_high_accumulation hH.le hd hsum'
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
