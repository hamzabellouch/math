import Mathlib
import OAI.Analysis.CoulombRadii.RadialBounds.PhysicalShellError
import OAI.Analysis.CoulombRadii.Propagation.InitialMesh
import OAI.Analysis.CoulombRadii.Packets.PhysicalRetainedDatum

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

theorem physical_barrier_data : ∃ ε B C L M : ℝ,0<ε ∧ 0<B ∧ 0 ≤ C ∧ 0 ≤ M ∧
    ∀ D : ℝ,0 ≤ D → ∃ s₀:ℝ,0<s₀ ∧ s₀ ≤ 1 ∧ ∀ s:ℝ,0<s → s<s₀ →
    ∃ Zmin:ℕ,∀ Z:ℕ,Zmin ≤ Z → ∀ (hZ:1 ≤ Z) {N K:ℕ}
      {ψ:Wavefunction (N+1)} {g:Gradient (N+1)},
    ∀ (hd:FormDomain ψ g) (hn:normSquared ψ=1),
    (∀ (χ:Wavefunction (N+1)) (h:Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E:ℝ},(E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → (N+1:ℝ) ≤ 3*(Z:ℝ) →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let r₀ := initialAtomicRadius ε (Z:ℝ)
    let P := observationLaw K (rawLaw ψ)
    let rs := fun j : Fin K => r₀*2^j.val
    ∀ (j : Fin K), rs j  ≤  s →
    ∃ d:PropagationDatum P B C (rs j) (Z:ℝ) L
      (fun o => conditionalPacketDensity P Prod.fst (tailObservation rs j.val)
        Coulomb.unitWindow 1 r₀ s (tailObservation rs j.val o)),
      (∫ o,(∫ x,d.error o x) ∂P) ≤ M*(rs j)^9 := by
  obtain ⟨εmax,hεmax,HI⟩ := physical_initial_event
  obtain ⟨ε,B,hε,hεceil,hB,hBe,hR,hbar⟩ := initial_constants_exist hεmax
  let C := max physicalSpatialCap (max B (32*ε^3))
  have hBC : B  ≤  C := (le_max_left _ _).trans (le_max_right _ _)
  have hcapC : physicalSpatialCap  ≤  C := le_max_left _ _
  have heC : 32*ε^3  ≤  C := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨k⟩ := propagation_constants_exist hB hBC
  obtain ⟨Kprob,hK,HG⟩ := physical_propagation_good_events Coulomb.unitWindow Coulomb.unitWindow_support
    Coulomb.unitWindow_mass Coulomb.unitWindow_radial (by norm_num : (0:ℝ)<1) hB hBC hcapC k
  obtain ⟨M,hM,HC⟩ := physical_bad_shell_error
  let T := 1029*ε^3+M*Real.sqrt Kprob
  have hT : 0  ≤  T := by dsimp [T]; positivity
  refine ⟨ε,B,C,k.L,T,hε,hB,hB.le.trans hBC,hT,?_⟩
  intro D hD
  obtain ⟨s₀,hs₀,hs₀1,hgates,HG⟩ := HG D hD
  refine ⟨s₀,hs₀,hs₀1,?_⟩
  intro s hs hss
  have hs1 : s  ≤  1 := hss.le.trans hs₀1
  obtain ⟨hq1,hq2,hDs⟩ := hgates hs hss
  obtain ⟨Zi,Hi⟩ := HI hε hεceil D Coulomb.unitWindow Coulomb.unitWindow_mass
    Coulomb.unitWindow_radial Coulomb.unitWindow_support (by norm_num : (0:ℝ)<1) hs hq1
  refine ⟨Zi,?_⟩
  intro Z hZi hZ N K ψ g hd hn hmin E hE he hnum
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  intro j hjs
  have hZpos : 0<(Z:ℝ) := by exact_mod_cast (zero_lt_one.trans_le hZ)
  let r₀ := initialAtomicRadius ε (Z:ℝ)
  have hr : 0<r₀ := initialAtomicRadius_pos hε hZpos
  have hrs : r₀ ≤ s := (le_mul_of_one_le_right hr.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n:=j.val))).trans hjs
  have hr1 : r₀ ≤ 1 := hrs.trans hs1
  let P := observationLaw K (rawLaw ψ)
  let rs := fun l:Fin K => r₀*2^l.val
  let ix : Fin j.val → Fin K := fun l => ⟨l.val,l.isLt.trans j.isLt⟩
  have hscale (l:Fin j.val) : rs (ix l) ≤ s :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) l.isLt.le) hr.le).trans hjs
  have hge (l:Fin j.val) : r₀ ≤ rs (ix l) := le_mul_of_one_le_right hr.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  obtain ⟨G₀,hG₀,hp₀,hlo⟩ := Hi Z hZi hZ (J:=K) hd hn hmin hE he hnum
  have HG' := fun l : Fin j.val => HG Z hZ hd hn hmin hE he hr hs hss (ix l) (hscale l)
  choose G hG hp HGood using HG'
  have hcost (l : Fin j.val) :
      (∫ o in (G l)ᶜ,∫ y in {y : Position | rs (ix l)  ≤  ‖y‖ ∧ ‖y‖<2*(rs (ix l))},
        conditionalPacketDensity P Prod.fst (tailObservation rs l.val) Coulomb.unitWindow 1 r₀ s
          (tailObservation rs l.val o) y ∂volume ∂P)  ≤  M*Real.sqrt Kprob*(rs (ix l))^9 := by
    exact HC Z hZ hd hn hE he hD Coulomb.unitWindow.continuous Coulomb.unitWindow_mass
      Coulomb.unitWindow_support (by norm_num : (0:ℝ)<1) hr hs (hge l) ((hscale l).trans hs1)
      ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hr.trans_le (hge l)).le (hscale l) 7) hD).trans hDs)
      hq2 hK.le rs l.val (hG l).2.compl (hp l)
  have HF := physical_finite_retained_datum Z hZ hd hn Coulomb.unitWindow_support Coulomb.unitWindow_mass
    (by norm_num : (0:ℝ)<1) hε hB hBC hr hr1 hs (mul_nonneg hM (Real.sqrt_nonneg Kprob)) hq2
    (initialAtomicRadius_cubic hZpos) hnum hBe heC hR hbar k hG₀ hp₀ hlo G
    (fun j => (hG j).1) HGood hcost
  exact HF
end NeutralAtom
end

end

end OAI
