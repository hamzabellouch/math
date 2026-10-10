import Mathlib

namespace OAI

section
section
noncomputable section
namespace SKRatioGaussian.PathBridge
open Real Set
open scoped BigOperators NNReal

theorem finite_time_mesh {T δ₀ : ℝ} (hT : 0<T) (hδ₀ : 0<δ₀) :
    ∃ m : ℕ, 0 < m ∧ ∃ δ : ℝ≥0, 0<δ ∧ (δ:ℝ)≤δ₀ ∧ (m:ℝ)*(δ:ℝ)=T ∧
      (∀ k : Fin m,(k:ℝ)*(δ:ℝ)∈Icc 0 T) ∧
      ∀ t∈Icc 0 T,∃ k : Fin m,∃ u∈Icc (0:ℝ) 1,t=(k:ℝ)*(δ:ℝ)+(δ:ℝ)*u := by
  obtain ⟨m,hm⟩ := exists_nat_gt (T/δ₀)
  have hm0 : 0 < m := by
    exact_mod_cast lt_trans (div_pos hT hδ₀) hm
  have hmr : 0<(m:ℝ) := by exact_mod_cast hm0
  let δ : ℝ≥0 := ⟨T/m,(div_pos hT hmr).le⟩
  have hδ : 0<(δ:ℝ) := div_pos hT hmr
  have he : (m:ℝ)*(δ:ℝ)=T := by
    change (m:ℝ)*(T/(m:ℝ))=T
    field_simp
  refine ⟨m,hm0,δ,hδ,?_,he,?_,?_⟩
  · change T/(m:ℝ)≤δ₀
    rw [div_le_iff₀ hmr]
    have h := (div_lt_iff₀ hδ₀).mp hm
    nlinarith
  · intro k
    constructor
    · positivity
    · have hk : (k:ℝ)<(m:ℝ) := by exact_mod_cast k.isLt
      nlinarith
  · intro t ht
    by_cases htop : t=T
    · let k : Fin m := ⟨m-1,by omega⟩
      refine ⟨k,1,by norm_num,?_⟩
      have hk : (k:ℝ)=(m:ℝ)-1 := by
        dsimp [k]
        rw [Nat.cast_sub (by omega)]
        norm_num
      rw [htop,hk]
      nlinarith
    · have hlt : t<T := lt_of_le_of_ne ht.2 htop
      have hx : 0≤t/(δ:ℝ) := div_nonneg ht.1 hδ.le
      have hxm : t/(δ:ℝ) < m := by rw [div_lt_iff₀ hδ];nlinarith
      have hfloor : ⌊t/(δ:ℝ)⌋₊ < m := (Nat.floor_lt hx).mpr hxm
      let k : Fin m := ⟨⌊t/(δ:ℝ)⌋₊,hfloor⟩
      let u := t/(δ:ℝ)-(k:ℝ)
      refine ⟨k,u,⟨?_,?_⟩,?_⟩
      · exact sub_nonneg.mpr (Nat.floor_le hx)
      · have hf := Nat.lt_floor_add_one (t/(δ:ℝ))
        dsimp [u,k]
        linarith
      · dsimp [u]
        field_simp
        ring
end SKRatioGaussian.PathBridge

end
end

section

noncomputable section

end
end
end

end OAI
