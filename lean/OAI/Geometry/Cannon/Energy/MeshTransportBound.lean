import Mathlib
import OAI.Geometry.Cannon.Modulus.RadialCellEnergy
import OAI.Geometry.Cannon.Energy.MeshEnergySumFilter

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
open Set MeasureTheory
open scoped BigOperators
open Set Topology

namespace CannonApprox

open Set Metric CannonCrossEnergy CannonPacking CannonTransfer

theorem exists_mesh_transport_bound {X : Type*} [MetricSpace X]
    (Q : ℕ) (CP H B : ℝ) (hpack : PolynomialPacking (X := X) Q CP)
    (hCP : 0 ≤ CP) (hH : 0 < H) (hB : 0 < B)
    (g : X ≃ₜ X)
    (hg : ∀ x y, dist (g x) (g y) ≤ H*dist x y)
    (hginv : ∀ x y, dist (g.symm x) (g.symm y) ≤ B*dist x y) :
    ∃ N : ℕ, ∀ (ι : Type*) [Fintype ι] (p : ι → X) (r J : ℝ),
      0 < r → 0 ≤ J → max H 1*r ≤ 1 →
      (∀ i j, i ≠ j → r ≤ dist (p i) (p j)) →
      (∀ x, ∃ i, dist (p i) x ≤ r) →
      ∀ (F : X → ℝ), BddAbove (range F) → BddBelow (range F) →
      ∀ K L : Set X,
      (∀ i, (ball (p i) (2*r) ∩ K).Nonempty →
        ∀ j, dist (p j) (g.symm (p i)) ≤ r → p j ∈ L) →
      meshEnergy p r J (F ∘ g.symm) K ≤ (N:ℝ)*meshEnergy p r (B*J+1) F L := by
  classical
  obtain ⟨N,hN⟩ := exists_overlap_bound Q CP H 1 hpack hCP hH (by norm_num)
  refine ⟨N,?_⟩
  intro ι hι p r J hr hJ hscale hpsep hpnet F hFhi hFlo K L hnear
  let α := {i : ι // (ball (p i) (2*r) ∩ K).Nonempty}
  let β := {j : ι // (ball (p j) (2*r) ∩ L).Nonempty}
  choose q hq using fun i : α => hpnet (g.symm (p i.val))
  have hqL (i : α) : p (q i) ∈ L := hnear i.val i.property (q i) (hq i)
  let σ : α → β := fun i => ⟨q i,⟨p (q i), by simp [hr],hqL i⟩⟩
  let w : β → ℝ := fun j => oscillation F (closedBall (p j.val) ((B*J+1)*r))
  have hosci (i : α) :
      (oscillation (F ∘ g.symm) (closedBall (p i.val) (J*r)))^2 ≤ (w (σ i))^2 := by
    have hsub : g.symm '' closedBall (p i.val) (J*r) ⊆
        closedBall (p (q i)) ((B*J+1)*r) := by
      rintro z ⟨y,hy,rfl⟩
      apply mem_closedBall.mpr
      have hd := dist_triangle (g.symm y) (g.symm (p i.val)) (p (q i))
      have h₁ := hginv y (p i.val)
      have h₂ := mul_le_mul_of_nonneg_left (mem_closedBall.mp hy) hB.le
      have h₃ : dist (g.symm (p i.val)) (p (q i)) ≤ r := by
        simpa only [dist_comm] using hq i
      nlinarith
    have hh := oscillation_mono_of_bounded F hFhi hFlo
      ((nonempty_closedBall.mpr (mul_nonneg hJ hr.le) :
        (closedBall (p i.val) (J*r)).Nonempty).image g.symm) hsub
    have heq : oscillation F (g.symm '' closedBall (p i.val) (J*r)) =
        oscillation (F ∘ g.symm) (closedBall (p i.val) (J*r)) := by
      simp only [CannonCrossEnergy.oscillation,image_image,Function.comp_def]
    rw [heq] at hh
    exact pow_le_pow_left₀ hh.1 hh.2 2
  have hcol (j : β) : (Finset.univ.filter (fun i : α => j ∈ ({σ i} : Finset β))).card ≤ N := by
    have hh := hN (fun i : α => p i.val) Finset.univ (g (p j.val)) r hr hscale (by
      intro i _ k _ hik
      simpa only [one_mul] using hpsep i.val k.val (fun heq => hik (Subtype.ext heq)))
    apply (Finset.card_le_card (s := Finset.univ.filter (fun i : α => j ∈ ({σ i} : Finset β))) ?_).trans hh
    intro i hi
    obtain ⟨_,hi⟩ := Finset.mem_filter.mp hi
    have heq : j = σ i := Finset.mem_singleton.mp hi
    have hqj : dist (p j.val) (g.symm (p i.val)) ≤ r := by
      rw [heq]
      exact hq i
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ i,?_⟩
    calc
      dist (g (p j.val)) (p i.val) = dist (g (p j.val)) (g (g.symm (p i.val))) := by simp
      _ ≤ H*dist (p j.val) (g.symm (p i.val)) := hg _ _
      _ ≤ H*r := mul_le_mul_of_nonneg_left hqj hH.le
  have he := overlap_energy (fun i : α => ({σ i} : Finset β)) w 1 N (by simp) hcol
  simp only [Finset.sum_singleton,Nat.cast_one,one_mul] at he
  exact (Finset.sum_le_sum (fun i _ => hosci i)).trans he

end CannonApprox

namespace CannonApprox

open Set Metric Filter Topology CannonPacking

theorem transported_mesh_energy_tendsto {X : Type*} [MetricSpace X] [CompactSpace X]
    (Q : ℕ) (CP H B : ℝ) (hpack : PolynomialPacking (X := X) Q CP)
    (hCP : 0 ≤ CP) (hH : 0 < H) (hB : 0 < B) (g : X ≃ₜ X)
    (hg : ∀ x y, dist (g x) (g y) ≤ H*dist x y)
    (hginv : ∀ x y, dist (g.symm x) (g.symm y) ≤ B*dist x y)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hpsep : ∀ n i j, i ≠ j → r n ≤ dist (p n i) (p n j))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ r n)
    (F : ℕ → X → ℝ) (hF : ∀ n, BddAbove (range (F n)) ∧ BddBelow (range (F n)))
    (b : X)
    (hE : ∀ L : Set X, IsCompact L → b ∉ L → ∀ J : ℝ, 0 < J →
      Tendsto (fun n => meshEnergy (p n) (r n) J (F n) L) atTop (𝓝 0))
    (K : Set X) (hK : IsCompact K) (hbK : g b ∉ K) (J : ℝ) (hJ : 0 < J) :
    Tendsto (fun n => meshEnergy (p n) (r n) J (F n ∘ g.symm) K) atTop (𝓝 0) := by
  classical
  by_cases hKn : K.Nonempty
  · let K₀ := g.symm '' K
    have hK₀ : IsCompact K₀ := hK.image g.symm.continuous
    obtain ⟨x,hx,hmin⟩ := hK₀.exists_isMinOn (hKn.image g.symm)
      (continuous_id.dist continuous_const).continuousOn
    have hxb : x ≠ b := by
      intro hxb
      obtain ⟨y,hy,heq⟩ := hx
      have heq' : y = g b := by simpa only [g.apply_symm_apply] using congrArg g (heq.trans hxb)
      exact hbK (heq' ▸ hy)
    have hd : 0 < dist x b := dist_pos.mpr hxb
    let L : Set X := {y | dist x b/2 ≤ dist y b}
    have hL : IsCompact L := (isClosed_le continuous_const
      (continuous_id.dist continuous_const)).isCompact
    have hbL : b ∉ L := by change ¬ dist x b/2 ≤ dist b b; rw [dist_self]; linarith
    obtain ⟨N,hN⟩ := exists_mesh_transport_bound Q CP H B hpack hCP hH hB g hg hginv
    have ht₁ : ∀ᶠ n in atTop, (1+2*B)*r n < dist x b/2 := by
      have hh : Tendsto (fun n => (1+2*B)*r n) atTop (𝓝 0) := by
        simpa only [mul_zero] using (tendsto_const_nhds.mul hrlim :
          Tendsto (fun n => (1+2*B)*r n) atTop (𝓝 ((1+2*B)*0)))
      exact hh.eventually_lt_const (by positivity)
    have ht₂ : ∀ᶠ n in atTop, max H 1*r n ≤ 1 := by
      have hh : Tendsto (fun n => max H 1*r n) atTop (𝓝 0) := by
        simpa only [mul_zero] using (tendsto_const_nhds.mul hrlim :
          Tendsto (fun n => max H 1*r n) atTop (𝓝 (max H 1*0)))
      exact (hh.eventually_lt_const zero_lt_one).mono (fun _ h => h.le)
    have hbound : ∀ᶠ n in atTop,
        meshEnergy (p n) (r n) J (F n ∘ g.symm) K ≤
          (N:ℝ)*meshEnergy (p n) (r n) (B*J+1) (F n) L := by
      filter_upwards [ht₁,ht₂] with n hn₁ hn₂
      apply hN (ι n) (p n) (r n) J (hr n) hJ.le hn₂ (hpsep n) (hpnet n)
        (F n) (hF n).1 (hF n).2 K L
      intro i hi j hj
      obtain ⟨y,hy,hyK⟩ := hi
      have hymem : g.symm y ∈ K₀ := mem_image_of_mem _ hyK
      have hdy : dist x b ≤ dist (g.symm y) b := hmin hymem
      have hyball : dist (p n i) y < 2*r n := by simpa only [mem_ball,dist_comm] using hy
      have hdist := dist_triangle (p n j) (g.symm (p n i)) (g.symm y)
      have hginvy := hginv (p n i) y
      have hmul := mul_lt_mul_of_pos_left hyball hB
      have hdj := dist_triangle (g.symm y) (p n j) b
      rw [dist_comm (g.symm y) (p n j)] at hdj
      change dist x b/2 ≤ dist (p n j) b
      nlinarith
    have hlim : Tendsto (fun n => (N:ℝ)*meshEnergy (p n) (r n) (B*J+1) (F n) L)
        atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds.mul (hE L hL hbL (B*J+1) (by positivity)) :
        Tendsto (fun n => (N:ℝ)*meshEnergy (p n) (r n) (B*J+1) (F n) L)
          atTop (𝓝 ((N:ℝ)*0)))
    exact squeeze_zero' (Eventually.of_forall (fun n => meshEnergy_nonneg _ _ _ _ _)) hbound hlim
  · have hKempty : K = ∅ := not_nonempty_iff_eq_empty.mp hKn
    simp [hKempty,meshEnergy_eq_sum_filter]

end CannonApprox

open Set Metric Filter Topology

end
end
end
end
end
end
end
end
end
end

end OAI
