import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodRegularity

namespace OAI

namespace ConvexSkorokhod

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def normalPartition (u k : ℝ → E) (y : ℕ → E) (m : ℕ) : ℝ :=
  ∑j∈Finset.range m,inner ℝ (u ((j:ℝ)/m)-y j) (k ((j+1:ℕ)/(m:ℝ))-k ((j:ℝ)/m))

end ConvexSkorokhod

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

lemma normal_block_bound (B : Body E) (x₀ : E) (w : ℕ → E) (a n : ℕ)
    (v y : E) (hy : y∈B.carrier) (δ : ℝ)
    (hclose : ∀ i < n,‖v-walk B x₀ w (a+i+1)‖ ≤ δ) :
    ⟪v-y,regulator B x₀ w (a+n)-regulator B x₀ w a⟫ ≤
      δ*(variation (regulator B x₀ w) (a+n)-variation (regulator B x₀ w) a) := by
  let k := regulator B x₀ w
  have hs := sum_inner_increment (fun i => k (a+i)) n (v-y)
  simp only [Nat.add_zero] at hs
  rw [real_inner_comm,←hs]
  have hterm : ∀i∈Finset.range n,
      ⟪k (a+(i+1))-k (a+i),v-y⟫ ≤ δ*‖k (a+(i+1))-k (a+i)‖ := by
    intro i hi
    let X := walk B x₀ w (a+i+1)
    have hn := regulator_normal B x₀ w (a+i) y hy
    have he : v-y=(v-X)-(y-X) := by abel
    rw [he,inner_sub_right]
    have hCS := (abs_le.mp (abs_real_inner_le_norm (k (a+(i+1))-k (a+i)) (v-X))).2
    have hv : ‖v-X‖ ≤ δ := hclose i (Finset.mem_range.mp hi)
    have hm := mul_le_mul_of_nonneg_left hv (norm_nonneg (k (a+(i+1))-k (a+i)))
    change 0 ≤ ⟪k (a+i+1)-k (a+i),y-X⟫ at hn
    rw [Nat.add_assoc] at hn
    linarith
  calc
    (∑i∈Finset.range n,⟪k (a+(i+1))-k (a+i),v-y⟫)
        ≤ ∑i∈Finset.range n,δ*‖k (a+(i+1))-k (a+i)‖ := Finset.sum_le_sum hterm
    _ = δ*variation (fun i => k (a+i)) n := by rw [←Finset.mul_sum];rfl
    _ = δ*(variation k (a+n)-variation k a) := by rw [variation_add];ring

lemma normal_coarse_bound (B : Body E) (x₀ : E) (w : ℕ → E) (q : ℕ → ℕ)
    (hq : Monotone q) (hq₀ : q 0=0) (m N : ℕ) (hqN : q m=N)
    (v y : ℕ → E) (hy : ∀ j < m,y j∈B.carrier) (δ : ℝ)
    (hclose : ∀ j < m,∀i,q j ≤ i → i<q (j+1) → ‖v j-walk B x₀ w (i+1)‖ ≤ δ) :
    (∑j∈Finset.range m,⟪v j-y j,regulator B x₀ w (q (j+1))-regulator B x₀ w (q j)⟫) ≤
      δ*variation (regulator B x₀ w) N := by
  have hb : ∀j∈Finset.range m,
      ⟪v j-y j,regulator B x₀ w (q (j+1))-regulator B x₀ w (q j)⟫ ≤
        δ*(variation (regulator B x₀ w) (q (j+1))-variation (regulator B x₀ w) (q j)) := by
    intro j hj
    have hle := hq (Nat.le_succ j)
    have he : q j+(q (j+1)-q j)=q (j+1) := Nat.add_sub_of_le hle
    have hh := normal_block_bound B x₀ w (q j) (q (j+1)-q j) (v j) (y j) (hy j (Finset.mem_range.mp hj)) δ
      (by intro i hi;apply hclose j (Finset.mem_range.mp hj) (q j+i) (by omega) (by omega))
    simpa only [he] using hh
  calc
    _ ≤ ∑j∈Finset.range m,δ*(variation (regulator B x₀ w) (q (j+1))-variation (regulator B x₀ w) (q j)) := Finset.sum_le_sum hb
    _ = δ*variation (regulator B x₀ w) N := by
      rw [←Finset.mul_sum,Finset.sum_range_sub (fun i => variation (regulator B x₀ w) (q i)),hqN,hq₀]
      simp [variation]

lemma mesh_at_sample (B : Body E) (x₀ : E) (w : ℝ → E) (N : ℕ) (hN : 0 < N) (i : ℕ) :
    mesh B x₀ w N ((i:ℝ)/N)=walk B x₀ (sampledDriver w N) i := by
  have hN' : (N:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
  simp only [mesh,div_mul_cancel₀ _ hN',Nat.floor_natCast]

lemma partition_sample_near (m N : ℕ) (hm : 0 < m) (hN : 0 < N)
    (j i : ℕ) (hj : j < m) (hi₀ : ⌊(j:ℝ)/m*N⌋₊ ≤ i) (hi₁ : i<⌊(j+1:ℕ)/(m:ℝ)*N⌋₊) :
    ((i+1:ℕ)/(N:ℝ))∈Icc (0:ℝ) 1 ∧
      |((i+1:ℕ)/(N:ℝ))-(j:ℝ)/m| < 1/(m:ℝ)+1/(N:ℝ) := by
  have hm' : (0:ℝ)< m := by exact_mod_cast hm
  have hN' : (0:ℝ)<N := by exact_mod_cast hN
  have hbase : (j:ℝ)/m∈Icc (0:ℝ) 1 := by
    refine ⟨by positivity,?_⟩
    rw [div_le_one hm'];exact_mod_cast hj.le
  have hnext : ((j+1:ℕ)/(m:ℝ))∈Icc (0:ℝ) 1 := by
    refine ⟨by positivity,?_⟩
    rw [div_le_one hm'];exact_mod_cast hj
  have hlow := (sample_floor_bounds N hN ((j:ℝ)/m) hbase.1).2
  have hl : (⌊(j:ℝ)/m*N⌋₊:ℝ)/N ≤ (i:ℝ)/N := div_le_div_of_nonneg_right (by exact_mod_cast hi₀) hN'.le
  have hu : ((i+1:ℕ):ℝ)/N ≤ ((j+1:ℕ):ℝ)/m := by
    apply le_trans _ (sample_floor_bounds N hN (((j+1:ℕ):ℝ)/m) hnext.1).1
    exact div_le_div_of_nonneg_right (by exact_mod_cast hi₁) hN'.le
  have hinc : (i:ℝ)/N < ((i+1:ℕ):ℝ)/N := (div_lt_div_iff_of_pos_right hN').mpr (by exact_mod_cast Nat.lt_succ_self i)
  have he : ((j+1:ℕ):ℝ)/m=(j:ℝ)/m+1/m := by push_cast;ring
  refine ⟨⟨by positivity,hu.trans hnext.2⟩,?_⟩
  rw [abs_lt]
  rw [he] at hu
  constructor <;> linarith [one_div_pos.mpr hm',one_div_pos.mpr hN']

end ConvexSkorokhod

end OAI
