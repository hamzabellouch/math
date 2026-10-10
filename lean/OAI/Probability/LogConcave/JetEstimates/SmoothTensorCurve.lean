import Mathlib
import OAI.Probability.LogConcave.Sampling.SpatialTensorContinuous

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open Set Function
open scoped Classical BigOperators Matrix.Norms.L2Operator

structure SmoothTensorCurve (d : ℕ) (A : ℕ → ℝ) (R b : ℝ)
    (X : ℝ × Point d → Point d) (V : ℝ → Point d → Point d) : Prop where
  smooth : ContDiff ℝ (⊤:ℕ∞) X
  initial : ∀y,X (0,y)=y
  equation : ∀t∈Icc 0 b,∀y,HasDerivAt (fun u => X (u,y)) (V t (X (t,y))) t
  velocity_smooth : ∀t∈Icc 0 b,ContDiff ℝ (⊤:ℕ∞) (V t)
  velocity_bound : ∀n t,t∈Icc 0 b → ∀y,
    AllSplitBound (multilinearTensor (iteratedFDeriv ℝ n (V t) y)) (A n/R^(n-1))

theorem smoothTensorCurve_bounds (A : ℕ → ℝ) (hA : ∀k,0≤A k) (n : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀(d : ℕ) (R b : ℝ) (X : ℝ × Point d → Point d)
      (V : ℝ → Point d → Point d), 0<R → R≤1 → 0≤b → b≤1 →
      SmoothTensorCurve d A R b X V → ∀t∈Icc 0 b,∀y,
      AllSplitBound (multilinearTensor (iteratedFDeriv ℝ n (fun z => X (t,z)) y))
        (C/R^(n-1)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      refine ⟨0,le_rfl,?_⟩
      intro d R b X V hR hR1 hb hb1 hX t ht y
      have he : (fun z => X (t,z))=(fun z => X (t,z)) := rfl
      let : Subsingleton (Unit ⊕ Fin 0) := ⟨by intro a b; cases a with
        | inl a => cases b with
          | inl b => rfl
          | inr b => exact Fin.elim0 b
        | inr a => exact Fin.elim0 a⟩
      exact allSplitBound_subsingleton _ _
    have hn0 : 0<n := Nat.pos_of_ne_zero hn
    choose C hC using fun k (hk : k<n) => ih k hk
    let B (k : ℕ) : ℝ := if hk : k<n then C k hk else 0
    have hB (k : ℕ) : 0≤B k := by
      dsimp [B]
      split_ifs with hk
      · exact (hC k hk).1
      · exact le_rfl
    let F : ℝ := ∑c : OrderedFinpartition n,A c.length*∏i,B (c.partSize i)
    let K : ℝ := (Fintype.card (OrderedFinpartition n):ℝ)*A 1
    have hF : 0≤F := Finset.sum_nonneg (fun c _ => mul_nonneg (hA _) (Finset.prod_nonneg (fun i _ => hB _)))
    have hK : 0≤K := mul_nonneg (Nat.cast_nonneg _) (hA 1)
    have hG := gronwallBound_mono (δ:=1) (by norm_num) hF hK
    have hG0 : 0≤gronwallBound 1 K F 1 := by
      have hh := hG (show (0:ℝ)≤1 by norm_num)
      rw [gronwallBound_x0] at hh
      linarith
    refine ⟨gronwallBound 1 K F 1,hG0,?_⟩
    intro d R b X V hR hR1 hb hb1 hX t ht y
    let T (u : ℝ) := multilinearTensor (iteratedFDeriv ℝ n (fun z => X (u,z)) y)
    let D (u : ℝ) := multilinearTensor (iteratedFDeriv ℝ n (fun z => V u (X (u,z))) y)
    have hpow : 0<R^(n-1) := pow_pos hR _
    have hinit : AllSplitBound (T 0) (1/R^(n-1)) := by
      have he : (fun z => X (0,z))=id := funext hX.initial
      dsimp only [T]
      rw [he]
      exact (multilinearTensor_id_bound y).mono (by norm_num)
        ((le_div_iff₀ hpow).mpr (by simpa using (pow_le_one₀ hR.le hR1 : R^(n-1)≤1)))
    have hd (u : ℝ) (hu : u∈Ico 0 b) : HasDerivWithinAt T (D u) (Ici u) u :=
      (spatialTensor_time_deriv hX.smooth (V u) u (hX.equation u ⟨hu.1,hu.2.le⟩) y).hasDerivWithinAt
    have hbound (u : ℝ) (hu : u∈Ico 0 b) :
        AllSplitBound (D u) (K*‖splitBundle (T u)‖+F/R^(n-1)) := by
      let z := ‖splitBundle (T u)‖
      let N (k : ℕ) : ℝ := if k<n then B k/R^(k-1) else z
      let M (k : ℕ) : ℝ := A k/R^(k-1)
      have hM (k : ℕ) : 0≤M k := div_nonneg (hA _) (pow_nonneg hR.le _)
      have hN (k : ℕ) : 0≤N k := by
        dsimp [N,z]
        split_ifs
        · exact div_nonneg (hB _) (pow_nonneg hR.le _)
        · exact norm_nonneg _
      have hlow (k : ℕ) (hk : k≤n) : AllSplitBound
          (multilinearTensor (iteratedFDeriv ℝ k (fun w => X (u,w)) y)) (N k) := by
        by_cases hkn : k<n
        · have hh := (hC k hkn).2 d R b X V hR hR1 hb hb1 hX u ⟨hu.1,hu.2.le⟩ y
          simpa only [N,B,dite_eq_left hkn,ite_eq_left hkn] using hh
        · have he : k=n := by omega
          subst k
          simpa only [N,lt_self_iff_false,ite_false,z,T] using allSplitBound_bundle (T u)
      have hs : ContDiffAt ℝ (n:ℕ) (fun w => X (u,w)) y :=
        (hX.smooth.comp (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))
      have hv : ContDiffAt ℝ (n:ℕ) (V u) (X (u,y)) :=
        (hX.velocity_smooth u ⟨hu.1,hu.2.le⟩).contDiffAt.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))
      have hh := iteratedFDeriv_comp_allSplit y hs hv M N hM hN
        (fun k hk => hX.velocity_bound k u ⟨hu.1,hu.2.le⟩ (X (u,y))) hlow
      have hp := partition_majorant_linear hM
        (fun k => div_nonneg (hB k) (pow_nonneg hR.le (k-1))) (norm_nonneg (splitBundle (T u)))
        (fun k hk => show N k=B k/R^(k-1) from ite_eq_left hk)
        (show N n=z from ite_eq_right (lt_irrefl n))
      have he : (∑c : OrderedFinpartition n,M c.length*∏i,(B (c.partSize i)/R^(c.partSize i-1)))=
          F/R^(n-1) := partition_sum_scale hn0 A B R
      rw [he] at hp
      have hp' : (∑c : OrderedFinpartition n,M c.length*∏i,N (c.partSize i))≤K*z+F/R^(n-1) := by
        simpa only [M,Nat.sub_self,pow_zero,div_one,K,mul_assoc] using hp
      exact hh.mono (Finset.sum_nonneg (fun c _ => mul_nonneg (hM _) (Finset.prod_nonneg (fun i _ => hN _)))) hp'
    have hg := allSplit_gronwall (spatialTensor_continuous hX.smooth y).continuousOn hd
      (div_nonneg (by norm_num) hpow.le) (div_nonneg hF hpow.le) hK hinit hbound ht
    rw [gronwallBound_div] at hg
    apply hg.mono (div_nonneg (by
      have hh := hG (show (0:ℝ)≤t-0 by linarith [ht.1])
      rw [gronwallBound_x0] at hh
      linarith) hpow.le)
    exact div_le_div_of_nonneg_right (hG (by linarith [ht.2])) hpow.le
end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
