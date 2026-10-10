import OAI.Analysis.AncientFlat.Geometry.InnerExtensionCore
import OAI.Analysis.AncientFlat.Regularity.HolderTimeChange

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff NNReal
namespace FlatWeighted
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
def clip01 (x : ℝ) : ℝ := min 1 (max 0 x)
lemma clip01_mem (x : ℝ) : clip01 x∈Icc (0:ℝ) 1 := by
  exact ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩
lemma clip01_lip (x y : ℝ) : |clip01 x-clip01 y|≤|x-y| := by
  have h := abs_min_sub_min_le_max (1:ℝ) (max 0 x) 1 (max 0 y)
  simp only [sub_self,abs_zero] at h
  rw [max_eq_right (abs_nonneg (max 0 x-max 0 y))] at h
  exact h.trans (by simpa only [max_comm] using abs_max_sub_max_le_abs x y 0)
lemma cutoff_clip {ψ : ℝ → ℝ} (hψ : ExtensionCutoff ψ) (s : ℝ) (hs : 0 ≤ s) :
    ψ (clip01 s)=ψ s := by
  by_cases h : s≤1
  · simp [clip01,max_eq_right hs,min_eq_right h]
  · have h1 := hψ.2.2.2 1 (by rfl)
    have hs1 := hψ.2.2.2 s (not_le.mp h).le
    simp [clip01,max_eq_right hs,min_eq_left (not_le.mp h).le,h1,hs1]
lemma cutoff_zero {ψ : ℝ → ℝ} (hψ : ExtensionCutoff ψ) : ψ 0=1 := by
  obtain ⟨ε,hε,he⟩ := hψ.2.2.1
  exact he 0 ⟨le_rfl,hε.le⟩
lemma inv_diff_bound {A B : ℝ} (hA : (1:ℝ)/4096≤A) (hB : (1:ℝ)/4096≤B) :
    |A⁻¹-B⁻¹|≤(4096:ℝ)^2*|A-B| := by
  have hAp : 0<A := by linarith
  have hBp : 0<B := by linarith
  have ha : A⁻¹≤4096 := (inv_le_iff_one_le_mul₀ hAp).mpr (by nlinarith)
  have hb : B⁻¹≤4096 := (inv_le_iff_one_le_mul₀ hBp).mpr (by nlinarith)
  have he : A⁻¹-B⁻¹=(B-A)*(A⁻¹*B⁻¹) := by field_simp
  rw [he,abs_mul,abs_mul,abs_of_pos (inv_pos.mpr hAp),abs_of_pos (inv_pos.mpr hBp),abs_sub_comm]
  have hab := mul_le_mul ha hb (inv_nonneg.mpr hBp.le) (by norm_num : (0:ℝ)≤4096)
  nlinarith [mul_le_mul_of_nonneg_left hab (abs_nonneg (A-B))]
def regularWeight (ψ : ℝ → ℝ) (T : ℝ) (p : V × ℝ) : ℝ :=
  ψ (clip01 ((-p.2-T)/(max (‖p.1‖^2+Real.sqrt T) ((1:ℝ)/64))^2))
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
lemma regularWeight_holder {ψ : ℝ → ℝ} (hψ : ExtensionCutoff ψ)
    (α : ℝ) (hα : 0<α) (hα1 : α≤1) :
    ∃ K : ℝ, 0<K ∧ ∀ T : ℝ, 0<T → T≤4 →
      HolderBound α {p : V × ℝ | ‖p.1‖≤2 ∧ -2≤p.2 ∧ p.2<0}
        (regularWeight ψ T) K := by
  obtain ⟨L,hL⟩ := (hψ.1.of_le (by simp : (1:ℕ∞ω)≤∞)).contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1:ℕ∞ω)≠0) (convex_Icc (0:ℝ) 1) isCompact_Icc
  let K : ℝ := 6000000000*(L:ℝ)+1
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨K,hK,fun T hT hT4 => ⟨?_,?_⟩⟩
  · intro p hp
    have hR := hψ.2.1 (clip01 ((-p.2-T)/(max (‖p.1‖^2+Real.sqrt T) ((1:ℝ)/64))^2)) (clip01_mem _).1
    simpa only [regularWeight,Real.norm_eq_abs,abs_of_nonneg hR.1] using
      hR.2.trans (show 1≤K by dsimp [K]; linarith [L.coe_nonneg])
  · intro p hp q hq
    have hR (p : V × ℝ) : 0≤regularWeight ψ T p ∧ regularWeight ψ T p≤1 :=
      hψ.2.1 _ (clip01_mem _).1
    by_cases hd : pdist p q≤1
    · let A := max (‖p.1‖^2+Real.sqrt T) ((1:ℝ)/64)
      let B := max (‖q.1‖^2+Real.sqrt T) ((1:ℝ)/64)
      have hA : (1:ℝ)/64≤A := le_max_right _ _
      have hB : (1:ℝ)/64≤B := le_max_right _ _
      have hTA : Real.sqrt T≤2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num; exact hT4⟩
      have hA6 : A≤6 := max_le (by nlinarith [norm_nonneg p.1,hp.1]) (by norm_num)
      have hB6 : B≤6 := max_le (by nlinarith [norm_nonneg q.1,hq.1]) (by norm_num)
      have hnorm : |‖p.1‖^2-‖q.1‖^2|≤4*‖p.1-q.1‖ := by
        rw [sq_sub_sq,abs_mul,abs_of_nonneg (by positivity : 0≤‖p.1‖+‖q.1‖)]
        nlinarith [abs_norm_sub_norm_le p.1 q.1,norm_nonneg (p.1-q.1),hp.1,hq.1,abs_nonneg (‖p.1‖-‖q.1‖)]
      have hAB : |A-B|≤4*‖p.1-q.1‖ := by
        exact (abs_max_sub_max_le_abs _ _ _).trans (by simpa only [add_sub_add_right_eq_sub] using hnorm)
      have hsAB : |A^2-B^2|≤48*‖p.1-q.1‖ := by
        rw [sq_sub_sq,abs_mul,abs_of_nonneg (by linarith : 0≤A+B)]
        nlinarith [abs_nonneg (A-B),norm_nonneg (p.1-q.1)]
      have hAsq : (1:ℝ)/4096≤A^2 := by nlinarith
      have hBsq : (1:ℝ)/4096≤B^2 := by nlinarith
      have hAp : 0<A^2 := by linarith
      have ha : (A^2)⁻¹≤4096 := (inv_le_iff_one_le_mul₀ hAp).mpr (by nlinarith)
      have hinv : |(A^2)⁻¹-(B^2)⁻¹|≤805306368*‖p.1-q.1‖ := by
        calc
          _ ≤ (4096:ℝ)^2*|A^2-B^2| := inv_diff_bound hAsq hBsq
          _ ≤ (4096:ℝ)^2*(48*‖p.1-q.1‖) := mul_le_mul_of_nonneg_left hsAB (by positivity)
          _ = _ := by ring
      have hnq : |-q.2-T|≤6 := abs_le.mpr ⟨by linarith [hq.2.2],by linarith [hq.2.1]⟩
      have hratio : |(-p.2-T)/A^2-(-q.2-T)/B^2|≤6000000000*pdist p q := by
        have he : (-p.2-T)/A^2-(-q.2-T)/B^2=
          (q.2-p.2)*(A^2)⁻¹+(-q.2-T)*((A^2)⁻¹-(B^2)⁻¹) := by ring
        rw [he]
        have ht : |q.2-p.2|≤pdist p q := by
          simpa only [Real.norm_eq_abs,Prod.snd_sub,abs_sub_comm] using
            (norm_snd_le (p-q)).trans (ParabolicLocalization.norm_pair_sub_le_pdist p q hd)
        have hx : ‖p.1-q.1‖≤pdist p q := le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)
        have hh := abs_add_le ((q.2-p.2)*(A^2)⁻¹) ((-q.2-T)*((A^2)⁻¹-(B^2)⁻¹))
        rw [abs_mul,abs_mul,abs_of_pos (inv_pos.mpr hAp)] at hh
        nlinarith [mul_le_mul ht ha (inv_nonneg.mpr hAp.le) (pdist_nonneg p q),
          mul_le_mul hnq hinv (abs_nonneg _) (by norm_num : (0:ℝ)≤6),pdist_nonneg p q]
      have hl := hL.norm_sub_le (clip01_mem ((-p.2-T)/A^2)) (clip01_mem ((-q.2-T)/B^2))
      change ‖regularWeight ψ T p-regularWeight ψ T q‖≤_ at hl
      have hc := clip01_lip ((-p.2-T)/A^2) ((-q.2-T)/B^2)
      simp only [Real.norm_eq_abs] at hl
      calc
        _ ≤ (L:ℝ)*(6000000000*pdist p q) := hl.trans (mul_le_mul_of_nonneg_left (hc.trans hratio) L.coe_nonneg)
        _ ≤ (L:ℝ)*(6000000000*pdist p q^α) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_le_one (pdist_nonneg _ _) hd hα1) (by norm_num)) L.coe_nonneg
        _ ≤ K*pdist p q^α := by dsimp [K]; nlinarith [Real.rpow_nonneg (pdist_nonneg p q) α]
    · have he : ‖regularWeight ψ T p-regularWeight ψ T q‖≤1 := by
        rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨by linarith [(hR p).1,(hR q).2],by linarith [(hR p).2,(hR q).1]⟩
      have hpow := Real.one_le_rpow (le_of_not_ge hd) hα.le
      have hk1 : 1≤K := by dsimp [K]; linarith [L.coe_nonneg]
      exact he.trans (by nlinarith)
end FlatWeighted

end

end OAI
