import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodGlobalVariation

namespace OAI

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma variation_reindex_le (k : ℕ → E) (φ : ℕ → ℕ) (N M : ℕ)
    (hφ : Monotone φ) (hmap : ∀i ≤ N,φ i ≤ M) :
    variation (k ∘ φ) N ≤ variation k M := by
  have hh := eVariationOn.comp_le_of_monotoneOn k φ (s:=Iic M) (t:=Iic N)
    (hφ.monotoneOn _) (fun i hi => hmap i hi)
  rw [eVariation_discrete,eVariation_discrete] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (variation_nonneg k M)).mp hh

lemma repeated_regulator_variation (B : Body E) (x₀ : E) (hx₀ : x₀∈B.carrier)
    (w : ℕ → E) (m n p : ℕ) (hn : 0 < n) (hp : p ≤ m*n) :
    variation (regulator B x₀ (fun i => w (i/n))) p ≤ variation (regulator B x₀ w) m := by
  have he : regulator B x₀ (fun i => w (i/n)) = regulator B x₀ w ∘ (fun i => i/n) := by
    funext i
    simp only [regulator,walk_repeat B x₀ hx₀ w n hn,Nat.zero_div,Function.comp_apply]
  rw [he]
  apply variation_reindex_le
  · exact fun i j hij => Nat.div_le_div_right hij
  · intro i hi
    apply Nat.div_le_of_le_mul
    simpa only [Nat.mul_comm] using hi.trans hp

lemma mesh_regulator_variation_of_bound (B : Body E) (x₀ : E) (w : ℝ → E)
    (N : ℕ) (hN : 0 < N) (C : ℝ)
    (hvar : variation (regulator B x₀ (sampledDriver w N)) N ≤ C) :
    eVariationOn (fun t : ℝ => regulator B x₀ (sampledDriver w N) ⌊t*N⌋₊) (Icc (0:ℝ) 1) ≤
      ENNReal.ofReal C := by
  have hN' : (0:ℝ)<N := by exact_mod_cast hN
  have hh := eVariationOn.comp_le_of_monotoneOn (regulator B x₀ (sampledDriver w N))
    (fun t : ℝ => ⌊t*N⌋₊) (s:=Iic N) (t:=Icc (0:ℝ) 1)
    (by intro s hs t ht hst;exact Nat.floor_mono (mul_le_mul_of_nonneg_right hst hN'.le))
    (by intro t ht;apply Nat.floor_le_of_le; nlinarith [ht.2])
  exact hh.trans ((eVariation_discrete _ _).le.trans (ENNReal.ofReal_le_ofReal hvar))

end ConvexSkorokhod

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma mesh_comparison_of_variation (B : Body E) (x₀ : E) (C δ η : ℝ)
    (hx₀ : x₀∈B.carrier) (w : ℝ → E)
    (hδ : 0 ≤ δ) (huc : ∀s∈Icc (0:ℝ) 1,∀t∈Icc (0:ℝ) 1,|s-t| < η → ‖w s-w t‖ ≤ δ)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : (1:ℝ)/m+1/n < η)
    (hvm : variation (regulator B x₀ (sampledDriver w m)) m ≤ C)
    (hvn : variation (regulator B x₀ (sampledDriver w n)) n ≤ C)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    ‖mesh B x₀ w m t-mesh B x₀ w n t‖ ≤ δ+Real.sqrt (4*δ*C) := by
  let p := ⌊t*((m*n:ℕ):ℝ)⌋₊
  have hp : p ≤ m*n := by
    apply Nat.floor_le_of_le
    simpa only [mul_one,one_mul] using mul_le_mul_of_nonneg_right ht.2 (Nat.cast_nonneg (m*n))
  let v₀ : ℕ → E := fun i => sampledDriver w m (i/n)
  let v₁ : ℕ → E := fun i => sampledDriver w n (i/m)
  have hv₀ : v₀ 0=w 0 := by simp [v₀,sampledDriver]
  have hv₁ : v₁ 0=w 0 := by simp [v₁,sampledDriver]
  have hvar₀ : variation (regulator B x₀ v₀) p ≤ C :=
    (repeated_regulator_variation B x₀ hx₀ (sampledDriver w m) m n p hn hp).trans hvm
  have hvar₁ : variation (regulator B x₀ v₁) p ≤ C :=
    (repeated_regulator_variation B x₀ hx₀ (sampledDriver w n) n m p hm (by simpa only [Nat.mul_comm] using hp)).trans hvn
  have hinput : ∀i ≤ p,‖(x₀+(v₀ i-v₀ 0))-(x₀+(v₁ i-v₁ 0))‖ ≤ δ := by
    intro i hi
    rw [hv₀,hv₁]
    have he : (x₀+(v₀ i-w 0))-(x₀+(v₁ i-w 0))=v₀ i-v₁ i := by abel
    rw [he]
    exact huc _ (sampled_time_bounds i m n hm hn (hi.trans hp)) _
      (sampled_time_bounds i n m hn hm (by simpa [Nat.mul_comm] using hi.trans hp))
      ((sampled_time_error i m n hm hn).trans_lt hmn)
  have hb := walk_driver_stability B x₀ x₀ hx₀ hx₀ v₀ v₁ p δ hδ hinput
  have hc : 2*δ*(variation (regulator B x₀ v₀) p+variation (regulator B x₀ v₁) p) ≤ 4*δ*C := by
    nlinarith [mul_le_mul_of_nonneg_left hvar₀ hδ,mul_le_mul_of_nonneg_left hvar₁ hδ]
  have hw₀ : walk B x₀ v₀ p=mesh B x₀ w m t := by
    rw [show v₀=fun i => sampledDriver w m (i/n) from rfl,walk_repeat B x₀ hx₀ _ n hn]
    unfold mesh
    congr 1
    exact floor_product_div t m n hn
  have hw₁ : walk B x₀ v₁ p=mesh B x₀ w n t := by
    rw [show v₁=fun i => sampledDriver w n (i/m) from rfl,walk_repeat B x₀ hx₀ _ m hm]
    unfold mesh
    congr 1
    simpa only [Nat.mul_comm] using floor_product_div t n m hm
  rw [hw₀,hw₁] at hb
  exact hb.trans (add_le_add le_rfl (Real.sqrt_le_sqrt hc))

end ConvexSkorokhod

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma mesh_modulus_of_variation (B : Body E) (x₀ : E) (C δ η : ℝ)
    (hx₀ : x₀∈B.carrier) (w : ℝ → E)
    (hδ : 0 ≤ δ) (huc : ∀s∈Icc (0:ℝ) 1,∀t∈Icc (0:ℝ) 1,|s-t|<η → ‖w s-w t‖ ≤ δ)
    (N : ℕ) (hN : 0 < N) (s t : ℝ) (hs : s∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (hvar : variation (regulator B x₀ (sampledDriver w N)) N ≤ C)
    (hst : |s-t|+1/(N:ℝ)<η) :
    ‖mesh B x₀ w N s-mesh B x₀ w N t‖ ≤ δ+Real.sqrt (2*δ*C) := by
  have hN' : (0:ℝ)<N := by exact_mod_cast hN
  have htime (i : ℕ) (hi : i ≤ N) : (i:ℝ)/N∈Icc (0:ℝ) 1 := by
    refine ⟨by positivity,?_⟩
    rw [div_le_one hN'];exact_mod_cast hi
  have ordered (s t : ℝ) (hs : s∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
      (hle : s ≤ t) (hst : t-s+1/(N:ℝ)<η) :
      ‖mesh B x₀ w N t-mesh B x₀ w N s‖ ≤ δ+Real.sqrt (2*δ*C) := by
    let a := ⌊s*N⌋₊
    let b := ⌊t*N⌋₊
    have hab : a ≤ b := Nat.floor_mono (mul_le_mul_of_nonneg_right hle hN'.le)
    have hb : b ≤ N := Nat.floor_le_of_le (by nlinarith [ht.2])
    have haa := sample_floor_bounds N hN s hs.1
    have hbb := sample_floor_bounds N hN t ht.1
    have he : a+(b-a)=b := Nat.add_sub_of_le hab
    have hh := walk_segment_displacement B x₀ hx₀ (sampledDriver w N) a (b-a) N (by omega) δ C hδ hvar
      (by
        intro i hi
        have hai : a+i ≤ b := by omega
        have hia : (a:ℝ)/N ≤ (a+i:ℕ)/N := div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_add_right a i) hN'.le
        have hit : ((a+i:ℕ):ℝ)/N ≤ t := (div_le_div_of_nonneg_right (by exact_mod_cast hai) hN'.le).trans hbb.1
        apply huc _ (htime _ (hai.trans hb)) _ (htime a (hab.trans hb))
        rw [abs_of_nonneg (sub_nonneg.mpr hia)]
        have haalo : s-1/(N:ℝ)<(a:ℝ)/N := haa.2
        linarith)
    simpa only [he,mesh] using hh
  rcases le_total s t with h|h
  · rw [norm_sub_rev]
    exact ordered s t hs ht h (by simpa only [abs_of_nonpos (sub_nonpos.mpr h),neg_sub] using hst)
  · exact ordered t s ht hs h (by simpa only [abs_of_nonneg (sub_nonneg.mpr h)] using hst)

end ConvexSkorokhod

end OAI
