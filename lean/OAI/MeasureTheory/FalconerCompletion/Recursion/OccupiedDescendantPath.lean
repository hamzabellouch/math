import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.BranchCounts
import OAI.MeasureTheory.Falconer.Recursion.BranchTransitions
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Estimates.ResidualFullChildNearFar
import OAI.MeasureTheory.FalconerCompletion.Graphs.PairAmbientGoodRadialIffDistanceGood
import OAI.MeasureTheory.FalconerCompletion.Recursion.Extend
import OAI.MeasureTheory.FalconerCompletion.Recursion.ProfileLipschitz
import OAI.MeasureTheory.FalconerCompletion.Recursion.RecursiveEnvironment

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ContDiff Classical ENNReal
variable {n : ℕ}

lemma occupiedDescendant_path (ρ : Measure (EuclideanSpace ℝ (Fin (n+1))))
    (P : CellPath (n+1)) {a b : ℕ} (hP : P.length=a) (hab : a≤b)
    (Z : Fin (n+1) → ℤ)
    (hZ : Z∈occupiedDescendantsND ρ a b (fun j => (pathIndex P j:ℤ))) :
    ∃ Q : CellPath (n+1), Q∈dyadicPaths b ∧ Q.take a=P ∧
      0<ρ (treeCell Q) ∧ treeCell Q=Attempt4FullFar.ambientGridCell b Z := by
  have hz := Finset.mem_filter.mp hZ
  obtain ⟨Q,hQ,hidx,hanc⟩ := exists_treePath_of_ambientDescendant P (hP ▸ hab) Z
    (by simpa only [hP] using hz.1)
  have he : treeCell Q=Attempt4FullFar.ambientGridCell b Z := by
    unfold treeCell; rw [hQ,hidx]; rfl
  exact ⟨Q,(mem_dyadicPaths b Q).mpr hQ,by simpa only [hP] using hanc,
    by rw [he]; exact pos_iff_ne_zero.mpr hz.2,he⟩

lemma RegularizedProfileData.occupiedDescendant_lower
    {ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))} {N B : ℕ} {s sig : ℝ} {m : ℝ → ℝ}
    (hd : RegularizedProfileData ρ N B s sig m)
    (P : CellPath (n+1)) {a b : ℕ} (hP : P.length=a) (hab : a≤b) (hb : b≤N)
    (Z : Fin (n+1) → ℤ)
    (hZ : Z∈occupiedDescendantsND ρ a b (fun j => (pathIndex P j:ℤ))) :
    ((2:ℝ)^N)^(-m b-(n+2:ℝ)*sig) ≤ (ρ (Attempt4FullFar.ambientGridCell b Z)).toReal := by
  obtain ⟨Q,hQ,hanc,hocc,he⟩ := occupiedDescendant_path ρ P hP hab Z hZ
  have hh := (hd.cells b hb Q ((mem_dyadicPaths b Q).mp hQ) hocc).1
  rw [he,←Real.rpow_add (by positivity : (0:ℝ)<2^N)] at hh
  convert hh using 1; congr 1; push_cast; ring

lemma recursive_near_max_le (e : RecursiveAngularND n) (h : ℕ) (hah : e.a≤h)
    (hX : e.X.length=e.a) (hY : e.Y.length=e.a)
    (_hx : e.ρ (treeCell e.X)≠0) (_hy : e.ρ (treeCell e.Y)≠0)
    (L₁ L₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (Q P : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) (Ψ : ℝ → ℝ) (M : ℝ)
    (hb : ∀ X Y : CellPath (n+1), X∈dyadicPaths h → Y∈dyadicPaths h →
      0<e.ρ (treeCell X) → 0<e.ρ (treeCell Y) →
      (e.successor h X Y).energy L₁ L₂ f g Q P Ψ≤M) :
    let X := fun j => (pathIndex e.X j:ℤ)
    let Y := fun j => (pathIndex e.Y j:ℤ)
    let A := occupiedDescendantsND e.ρ e.a h X
    let B := occupiedDescendantsND e.ρ e.a h Y
    ∀ hAB : (A.product B).Nonempty,
    Attempt4Near.graphChildMaxND (n+1)
      (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))) h e.v Ψ A B hAB
      (originalCellTransformND e.ρ h (((2:ℝ)^e.N)^(-e.mass h)) (e.symbol L₁ f Q h))
      (originalCellTransformND e.ρ h (((2:ℝ)^e.N)^(-e.mass h)) (e.symbol L₂ g P h))≤M := by
  dsimp only
  intro hAB
  apply Finset.sup'_le
  intro z hz
  obtain ⟨X,hXp,hXa,hXo,hXg⟩ := occupiedDescendant_path e.ρ e.X hX hah z.1 (Finset.mem_product.mp hz).1
  obtain ⟨Y,hYp,hYa,hYo,hYg⟩ := occupiedDescendant_path e.ρ e.Y hY hah z.2 (Finset.mem_product.mp hz).2
  have hh := hb X Y hXp hYp hXo hYo
  change _root_.OAI.Attempt4Near.sourceAngularHND (n+1)
    (_root_.OAI.Attempt4FullFar.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))) h e.v Ψ
    (fun z => _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ (treeCell X)
      (((2:ℝ)^e.N)^(-e.mass h)) (e.symbol L₁ f Q h) z.1 z.2)
    (fun z => _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ (treeCell Y)
      (((2:ℝ)^e.N)^(-e.mass h)) (e.symbol L₂ g P h) z.1 z.2)≤M at hh
  rw [hXg,hYg] at hh
  exact hh

lemma recursive_far_max_le (e : RecursiveAngularND n) [IsFiniteMeasure e.ρ]
    (b : ℕ) (hab : e.a≤b) (hX : e.X.length=e.a) (hY : e.Y.length=e.a)
    {K M : ℝ} (hK : 32*(n+2:ℝ)≤K) (hM : 0≤M)
    (hb : ∀ X Y : CellPath (n+1), X∈dyadicPaths b → Y∈dyadicPaths b →
      0<e.ρ (treeCell X) → 0<e.ρ (treeCell Y) →
      farSeparatedGridND b K (fun j => (pathIndex X j:ℤ)) (fun j => (pathIndex Y j:ℤ)) →
      (e.toRecursiveEnvironmentND.distanceData b e.v (e.i+1) X Y).coincidence.toReal≤M) :
    (farChildMaximumND e.ρ e.ρ b
      (occupiedFarPairsND e.ρ e.a b K (fun j => (pathIndex e.X j:ℤ)))
      (occupiedFarPairsND e.ρ e.a b K (fun j => (pathIndex e.Y j:ℤ)))
      e.v (((2:ℝ)^e.N)^(-e.mass b))
      (actualPairAmbientGood e.profile e.N e.q b e.v e.ρ e.mass e.sig e.C e.J (e.i+1))
      (actualPairAmbientGood e.profile e.N e.q b e.v e.ρ e.mass e.sig e.C e.J (e.i+1))).toReal≤M := by
  have one (P : CellPath (n+1)) (hP : P.length=e.a) :
      (occupiedFarPairsND e.ρ e.a b K (fun j => (pathIndex P j:ℤ))).sup
        (fun p => positiveDistanceCountND
          ((gridPairMeasureND e.ρ b p).restrict {z | euclideanPairDirectionND z∈
            actualPairAmbientGood e.profile e.N e.q b e.v e.ρ e.mass e.sig e.C e.J (e.i+1) z})
          (n+1) e.v b (((2:ℝ)^e.N)^(-e.mass b)))≤ENNReal.ofReal M := by
    apply Finset.sup_le
    intro p hp
    obtain ⟨X,Y,hX,hY,hXa,hYa,hXp,hYp,hXo,hYo,he⟩ :=
      occupiedFarPair_actual_state e.ρ e.mass e.N e.q b e.v e.sig e.C e.J (e.i+1)
        P (hP ▸ hab) hK p (by simpa only [hP] using hp)
    have hsep := (mem_farParentPairsND_iff.mp (Finset.mem_filter.mp hp).1).2.2
    have hs : farSeparatedGridND b K (fun j => (pathIndex X j:ℤ)) (fun j => (pathIndex Y j:ℤ)) := by
      rwa [hXp,hYp]
    have hh := hb X Y ((mem_dyadicPaths b X).mpr hX) ((mem_dyadicPaths b Y).mpr hY)
      (pos_iff_ne_zero.mpr hXo) (pos_iff_ne_zero.mpr hYo) hs
    apply (ENNReal.toReal_le_toReal (positiveDistanceCountND_ne_top _ _ _ _ _)
      ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hM]
    dsimp only [RecursiveAngularND.profile,RecursiveEnvironmentND.profile]
    rw [he]
    exact hh
  exact (ENNReal.toReal_le_toReal (farChildMaximumND_ne_top _ _ _ _ _ _ _ _ _)
    ENNReal.ofReal_ne_top).mpr (sup_le (one e.X hX) (one e.Y hY)) |>.trans (by simp [hM])

theorem uniform_recursive_near_far
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hsupp : tsupport Ψ⊆Ioo (1/4:ℝ) 4)
    (hΨpos : ∀ t,0≤Ψ t) {sig : ℝ} (hsig : 0<sig) (hsig₁ : sig≤1)
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (B total : ℕ) (hW : ∀ L∈W,L.length≤B)
    {Jmask : ℕ} (hJmask : 0<Jmask) (Cq : ℝ) (hCq : 0≤Cq)
    (T D : ℝ) (ell : ℕ) (hK : 32*(n+2:ℝ)≤(2:ℝ)^ell) :
    ∃ M : ℕ, ∃ Dnear H : ℝ,1≤Dnear ∧ 0≤H ∧ ∃ N₀ : ℕ, ∀ e : RecursiveAngularND n,
      N₀≤e.N → e.sig=sig → e.J=Jmask →
      ∀ B₀ s,RegularizedProfileData e.ρ e.N B₀ s sig e.mass →
      0<e.q → e.t₀≤e.N → e.a₀≤e.a → e.v≤e.t₀ →
      ∀ h : ℕ,e.a<h → h+ell+2≤e.N →
      ((h+ell+2:ℕ):ℝ)≤(e.v:ℝ)-2*(max ((e.retainedList e.a).sup descriptorLength)
        (Nat.ceil (10*sig*e.N)):ℕ)+D →
      e.X∈dyadicPaths e.a → e.Y∈dyadicPaths e.a → 0<e.ρ (treeCell e.X) → 0<e.ρ (treeCell e.Y) →
      ∀ (L₁ L₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (Q P : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
        (Mn : ℝ) (Mf : ℕ → ℝ),
      Measurable f → Measurable g → (∀ x,‖f x‖≤1) → (∀ x,‖g x‖≤1) →
      (∀ b∈e.fullList,L₁ b∈W) → (∀ b∈e.fullList,L₂ b∈W) →
      (∑ b∈e.fullList,(L₁ b).length)≤total → (∑ b∈e.fullList,(L₂ b).length)≤total →
      (∀ j≤M,∀ w,‖w‖=1 → ‖iteratedFDeriv ℝ j Q.1 w‖≤Cq) →
      (∀ j≤M,∀ w,‖w‖=1 → ‖iteratedFDeriv ℝ j P.1 w‖≤Cq) →
      (∀ X Y : CellPath (n+1),X∈dyadicPaths h → Y∈dyadicPaths h →
        0<e.ρ (treeCell X) → 0<e.ρ (treeCell Y) →
        (e.successor h X Y).energy L₁ L₂ f g Q P Ψ≤Mn) →
      (∀ b∈Finset.Icc (e.a+1) (h+ell+2),0≤Mf b) →
      (∀ b∈Finset.Icc (e.a+1) (h+ell+2),∀ X Y : CellPath (n+1),
        X∈dyadicPaths b → Y∈dyadicPaths b → 0<e.ρ (treeCell X) → 0<e.ρ (treeCell Y) →
        farSeparatedGridND b ((2:ℝ)^ell) (fun j => (pathIndex X j:ℤ)) (fun j => (pathIndex Y j:ℤ)) →
        (e.toRecursiveEnvironmentND.distanceData b e.v (e.i+1) X Y).coincidence.toReal≤Mf b) →
      e.energy L₁ L₂ f g Q P Ψ≤
        (20*(n+2:ℝ)+5)^(2*(n+1))*Dnear^(4*total)*
          ((2:ℝ)^e.N)^(-2*(e.profile h-e.profile e.a)+4*(n+2:ℝ)*sig)*Mn+
        H*(∑ b∈Finset.Icc (e.a+1) (h+ell+2),
          ((2:ℝ)^e.N)^(-2*(e.profile b-e.profile e.a)+4*(n+2:ℝ)*sig)*Mf b)+
        ((2:ℝ)^e.N)^(-T) := by
  have hs : ∀ t,Ψ t≠0 → t∈Ioo (1/4:ℝ) 4 :=
    fun t ht => hsupp (subset_closure ht)
  obtain ⟨J,Dnear,H,hDn,hH,hnf⟩ := actual_residual_full_child_near_farND
    hΨ hs hΨpos hsig hsig₁ W B total hW hJmask Cq hCq ((n+2:ℝ)*sig) T D ell hK
  obtain ⟨N₀,hnf⟩ := eventually_atTop.mp hnf
  refine ⟨2*(J+1)+n+3,Dnear,H,hDn,hH,N₀,?_⟩
  intro e hN he hJe B₀ s hd hq ht₀ ha₀ hv₀ h hah hhN hdepth hX hY hoccX hoccY
    L₁ L₂ f g Q P Mn Mf hf hg hfn hgn hL₁ hL₂ ht₁ ht₂ hQ hP hn hm hfar
  let := hd.probability
  have hXlen := (mem_dyadicPaths e.a e.X).mp hX
  have hYlen := (mem_dyadicPaths e.a e.Y).mp hY
  have hXgrid : treeCell e.X=Attempt4FullFar.ambientGridCell e.a (fun j => (pathIndex e.X j:ℤ)) := by
    unfold treeCell; rw [hXlen]; rfl
  have hYgrid : treeCell e.Y=Attempt4FullFar.ambientGridCell e.a (fun j => (pathIndex e.Y j:ℤ)) := by
    unfold treeCell; rw [hYlen]; rfl
  have hx : e.ρ (Attempt4FullFar.ambientGridCell e.a (fun j => (pathIndex e.X j:ℤ)))≠0 := by
    rw [←hXgrid]; exact ne_of_gt hoccX
  have hy : e.ρ (Attempt4FullFar.ambientGridCell e.a (fun j => (pathIndex e.Y j:ℤ)))≠0 := by
    rw [←hYgrid]; exact ne_of_gt hoccY
  have hup (Z : CellPath (n+1)) (hZ : Z.length=e.a) (ho : 0<e.ρ (treeCell Z)) :
      (e.ρ (Attempt4FullFar.ambientGridCell e.a (fun j => (pathIndex Z j:ℤ)))).toReal≤
        ((2:ℝ)^e.N)^(-e.mass e.a+(n+2:ℝ)*sig) := by
    have hz := (hd.cells e.a (by omega) Z hZ ho).2
    rw [←Real.rpow_add (by positivity : (0:ℝ)<2^e.N)] at hz
    have hc : treeCell Z=Attempt4FullFar.ambientGridCell e.a (fun j => (pathIndex Z j:ℤ)) := by
      unfold treeCell; rw [hZ]; rfl
    rw [hc] at hz
    convert hz using 1; congr 1; push_cast; ring
  have hlow (Z : CellPath (n+1)) (hZ : Z.length=e.a) :
      ∀ b∈Finset.Icc (e.a+1) (h+ell+2),∀ z∈occupiedDescendantsND e.ρ e.a b (fun j => (pathIndex Z j:ℤ)),
      ((2:ℝ)^e.N)^(-e.mass b-(n+2:ℝ)*sig)≤(e.ρ (Attempt4FullFar.ambientGridCell b z)).toReal := by
    intro b hb z hz
    have hb' := Finset.mem_Icc.mp hb
    exact hd.occupiedDescendant_lower Z hZ (by omega) (by omega) z hz
  have hvN : (e.v:ℝ)-(e.a:ℝ)≤e.N := by
    have := (Nat.cast_le (α:=ℝ)).mpr (hv₀.trans ht₀)
    have := Nat.cast_nonneg (α:=ℝ) e.a
    linarith
  have hh := hnf e.N hN e.ρ e.ρ e.profile e.q e.a₀ e.t₀ e.a h e.v hq ht₀ ha₀ hv₀
    L₁ L₂ e.mass e.C e.i f g Q P (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ))
    e.v (e.mass e.a) (fun b => e.mass b) hf hg hfn hgn hL₁ hL₂ ht₁ ht₂ hQ hP hx hy hah hvN hdepth
    (hlow e.X hXlen) (hlow e.Y hYlen) (hup e.X hXlen hoccX) (hup e.Y hYlen hoccY)
  dsimp only at hh
  rw [←he,←hJe] at hh
  have hnear := recursive_near_max_le e h hah.le hXlen hYlen (ne_of_gt hoccX) (ne_of_gt hoccY)
    L₁ L₂ f g Q P Ψ Mn hn
  have hfars (b : ℕ) (hb : b∈Finset.Icc (e.a+1) (h+ell+2)) :=
    recursive_far_max_le e b (by have := (Finset.mem_Icc.mp hb).1; omega) hXlen hYlen hK (hm b hb) (hfar b hb)
  have hdprof (b : ℕ) : e.mass b-(n+1:ℝ)*(b:ℝ)/(2*e.N)=e.profile b := by
    dsimp [RecursiveAngularND.profile,RecursiveEnvironmentND.profile,adjustedProfile]
    push_cast; ring
  have hn' := hnear ((original_occupied_nonemptyND e.ρ hah.le _ hx).product
    (original_occupied_nonemptyND e.ρ hah.le _ hy))
  have hdom := add_le_add
    (add_le_add
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn' (by positivity : 0≤Dnear^(4*total)))
        (by positivity : 0≤(20*(n+2:ℝ)+5)^(2*(n+1))*
        ((2:ℝ)^e.N)^(-2*((e.mass h-(n+1:ℝ)*(h:ℝ)/(2*e.N))-(e.mass e.a-(n+1:ℝ)*(e.a:ℝ)/(2*e.N)))+4*((n+2:ℝ)*e.sig))))
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun b hb =>
        mul_le_mul_of_nonneg_left (hfars b hb) (by positivity : 0≤
          ((2:ℝ)^e.N)^(-2*((e.mass b-(n+1:ℝ)*(b:ℝ)/(2*e.N))-(e.mass e.a-(n+1:ℝ)*(e.a:ℝ)/(2*e.N)))+4*((n+2:ℝ)*e.sig))))) hH))
    (le_refl (((2:ℝ)^e.N)^(-T)))
  have hfinal := hh.trans hdom
  conv_lhs at hfinal => unfold originalCellTransformND
  change treeCell e.X=GraphLiteralSupport.CurrentFalconer.ambientGridCell e.a (fun j => (pathIndex e.X j:ℤ)) at hXgrid
  change treeCell e.Y=GraphLiteralSupport.CurrentFalconer.ambientGridCell e.a (fun j => (pathIndex e.Y j:ℤ)) at hYgrid
  rw [←hXgrid,←hYgrid] at hfinal
  change e.energy L₁ L₂ f g Q P Ψ≤_ at hfinal
  simp only [hdprof] at hfinal
  rw [he] at hfinal
  convert hfinal using 1; ring_nf

end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.DimensionalPolicy
open PlanarFalconer

theorem weighted_branch_energy_induction (A : ℕ → ℝ) (N q offset D : ℕ)
    (sig K lam eps C terminal floor error L E : ℝ) (root : BranchState)
    (energies : BranchState → ℝ → Prop)
    (hN : 0 < N) (hq : 0 < q) (hsig : 0 < sig)
    (hC : 1 ≤ C) (hL : 0 ≤ L) (hE : 0 ≤ E)
    (hvalid : ∀ s u l, s.Valid N sig → BranchStep A N q offset sig s l u → u.Valid N sig)
    (hdepth : ∀ n, ∀ b : PolicyBranch A N q offset sig n, b.state 0 = root → n ≤ D)
    (hterminal : ∀ s, s.Valid N sig → s.finish ≤ s.start+100*q →
      ∀ x, energies s x → x ≤ terminal)
    (hreduction : ∀ s, s.Valid N sig →
      (∃ n, ∃ b : PolicyBranch A N q offset sig n, b.state 0 = root ∧ b.state n = s) →
      s.start+100*q < s.finish →
      ∀ M : ℝ, 0 ≤ M → floor ≤ M →
      (∀ u l, BranchStep A N q offset sig s l u → ∀ x, energies u x →
        ((2:ℝ)^N)^(branchExponentND A K lam sig eps s l u)*x ≤ M) →
      ∀ x, energies s x → x ≤ C*M+error)
    (htermWeight : ∀ n, ∀ b : PolicyBranch A N q offset sig n, b.state 0 = root →
      b.weight K lam eps*terminal ≤ L)
    (hfloorWeight : ∀ n, ∀ b : PolicyBranch A N q offset sig n, b.state 0 = root →
      b.weight K lam eps*floor ≤ L)
    (herrorWeight : ∀ n, ∀ b : PolicyBranch A N q offset sig n, b.state 0 = root →
      b.weight K lam eps*error ≤ E) :
    ∀ n, ∀ b : PolicyBranch A N q offset sig n, b.state 0 = root →
      ∀ x, energies (b.state n) x →
      b.weight K lam eps*x ≤ (C+1)^(D-n+1)*(L+E) := by
  have haux : ∀ s : BranchState, ∀ n, ∀ b : PolicyBranch A N q offset sig n,
      b.state 0 = root → b.state n = s → ∀ x, energies s x →
      b.weight K lam eps*x ≤ (C+1)^(D-n+1)*(L+E) := by
    intro s
    induction s using (measure (fun s : BranchState => s.finish-s.start)).wf.induction with
    | h s ih =>
      intro n b hroot hlast x hx
      have hs : s.Valid N sig := hlast ▸ b.valid n le_rfl
      have hW := b.weight_pos K lam eps
      have hsum : 0 ≤ L+E := add_nonneg hL hE
      have hpow : 1 ≤ (C+1)^(D-n) := one_le_pow₀ (by linarith)
      let H := (C+1)^(D-n)*(L+E)
      have hLH : L ≤ H := by dsimp only [H]; nlinarith
      have hEH : E ≤ H := by dsimp only [H]; nlinarith
      have hH : 0 ≤ H := hL.trans hLH
      have hHlast : H ≤ (C+1)^(D-n+1)*(L+E) := by
        rw [pow_succ]
        change H ≤ (C+1)^(D-n)*(C+1)*(L+E)
        nlinarith
      by_cases hw : s.finish ≤ s.start+100*q
      · have ht := hterminal s hs hw x hx
        exact ((mul_le_mul_of_nonneg_left ht hW.le).trans (htermWeight n b hroot)).trans
          (hLH.trans hHlast)
      · have hfloor : floor ≤ H/b.weight K lam eps := by
          apply (le_div_iff₀ hW).mpr
          simpa only [mul_comm] using (hfloorWeight n b hroot).trans hLH
        have hchildren : ∀ u l, BranchStep A N q offset sig s l u → ∀ y, energies u y →
            ((2:ℝ)^N)^(branchExponentND A K lam sig eps s l u)*y ≤ H/b.weight K lam eps := by
          intro u l hstep y hy
          have hu := hvalid s u l hs hstep
          have hstep' : BranchStep A N q offset sig (b.state n) l u := hlast ▸ hstep
          let b' := b.extend hu hstep'
          have hroot' : b'.state 0 = root := by
            change (b.extend hu hstep').state 0 = root
            rw [b.extend_state_le hu hstep' (Nat.zero_le n),hroot]
          have hlast' : b'.state (n+1) = u := b.extend_last_state hu hstep'
          have hnd := hdepth (n+1) b' hroot'
          have hi := ih u (hstep.width_decreases hN hq hsig hs hu) (n+1) b' hroot' hlast' y hy
          have harith : D-(n+1)+1 = D-n := by omega
          rw [harith] at hi
          change b'.weight K lam eps*y ≤ H at hi
          dsimp only [b'] at hi
          rw [b.weight_extend,hlast] at hi
          apply (le_div_iff₀ hW).mpr
          nlinarith only [hi]
        have hred := hreduction s hs ⟨n,b,hroot,hlast⟩ (by omega) (H/b.weight K lam eps)
          (div_nonneg hH hW.le) hfloor hchildren x hx
        have hh := mul_le_mul_of_nonneg_left hred hW.le
        have herr := herrorWeight n b hroot
        have hid : b.weight K lam eps*(C*(H/b.weight K lam eps)+error) =
            C*H+b.weight K lam eps*error := by field_simp
        rw [hid] at hh
        calc
          b.weight K lam eps*x ≤ C*H+E := by linarith
          _ ≤ (C+1)*H := by linarith
          _ = (C+1)^(D-n+1)*(L+E) := by dsimp only [H]; rw [pow_succ]; ring
  intro n b hr x hx
  exact haux (b.state n) n b hr rfl x hx

end GraphLiteralSupport.CurrentFalconer.DimensionalPolicy
end
end

end OAI
