import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowJetVariation
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowJetGronwall

namespace OAI

/-! Uniform higher-jet bounds for a local representative. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace ContinuumCoulomb

theorem flow_local_higher_bound (H W : ℝ × Position → Position)
    (hH : ContDiff ℝ 4 H) (hW : ContDiff ℝ 4 W)
    (O : Set Position) (hO : IsOpen O) (x : Position) (hx : x ∈ O)
    (hinit : ∀ y ∈ O, H (0,y) = y)
    (hODE : ∀ y ∈ O, ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun s => H (s,y)) (W (t,H (t,y))) t)
    (k : ℕ) (hk0 : 1 ≤ k) (hk : k ≤ 3)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ∀ j, 1 ≤ j → j ≤ k+1 →
      ‖iteratedFDeriv ℝ j (fun z => W (t,z)) (H (t,x))‖ ≤ B)
    (hprev : ∀ t ∈ Icc (0:ℝ) 1, ∀ j, 1 ≤ j → j ≤ k →
      ‖iteratedFDeriv ℝ j (fun y => H (t,y)) x‖ ≤ D^j)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖iteratedFDeriv ℝ (k+1) (fun y => H (t,y)) x‖ ≤
      ((k:ℝ)*2^k*(k.factorial:ℝ)*B*D^(k+1)) * Real.exp (B+1) := by
  let K : ℝ × Position → Position := fun p => W (p.1,H p)
  have hK : ContDiff ℝ 4 K := hW.comp (contDiff_fst.prodMk hH)
  let J : ℝ → SpatialJet (k+1) := fun s => iteratedFDeriv ℝ (k+1) (fun y => H (s,y)) x
  let dJ : ℝ → SpatialJet (k+1) := fun s => iteratedFDeriv ℝ (k+1) (fun y => K (s,y)) x
  have hd (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivWithinAt J (dJ s) (Icc (0:ℝ) 1) s :=
    flow_model_jet_derivative H K hH hK O hO x hx hODE (k+1) (by omega) s hs
  have hz : ‖J 0‖ = 0 := by
    have heq : (fun y => H (0,y)) =ᶠ[𝓝 x] (id : Position → Position) := by
      filter_upwards [hO.mem_nhds hx] with y hy
      exact hinit y hy
    change ‖iteratedFDeriv ℝ (k+1) (fun y => H (0,y)) x‖ = 0
    rw [(heq.iteratedFDeriv ℝ (k+1)).eq_of_nhds,←norm_iteratedFDeriv_fderiv]
    have hid : fderiv ℝ (id : Position → Position) =
        fun _ => ContinuousLinearMap.id ℝ Position := funext (fun y => fderiv_id (x := y))
    rw [hid]
    obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [hm,iteratedFDeriv_succ_const]
    simp
  have hb' (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      ‖dJ s‖ ≤ B*‖J s‖ + (k:ℝ)*2^k*(k.factorial:ℝ)*B*D^(k+1) := by
    have hf : ContDiff ℝ 4 (fun y => H (s,y)) := hH.comp (contDiff_const.prodMk contDiff_id)
    have hg : ContDiff ℝ 4 (fun y => W (s,y)) := hW.comp (contDiff_const.prodMk contDiff_id)
    exact flow_composition_highest_bound (fun y => H (s,y)) (fun y => W (s,y))
      hf hg k hk x B D hB hD (hb s hs) (hprev s hs)
  exact flow_inhomogeneous_bound J dJ B _ hB (by positivity) hd hz hb' t ht

end ContinuumCoulomb

end

end OAI
