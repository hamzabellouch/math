import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CubePolynomials01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open scoped ComplexConjugate
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace FactorProgression
open CubeFaces CubePolynomials
variable {G : Type*} [Group G]

lemma affine_polynomial (H : Filtration G) {k : ℕ} {f : ℤ → G}
    (hf : f∈polynomials H k) (a b : ℤ) :
    (fun z => f (a*z+b))∈polynomials H k := by
  rw [mem_polynomials] at hf ⊢
  intro I h n
  convert hf I (fun i => a*h i) (a*n+b) using 1
  ext v
  change f (a*(n+∑ i∈v∩I,h i)+b)=f (a*n+b+∑ i∈v∩I,a*h i)
  rw [← Finset.mul_sum]
  congr 1
  ring

lemma conjugate_polynomial (H : Filtration G) (h0 : H.level 0=⊤)
    {f : ℤ → G} (hf : f∈polynomials H 0) (v : G) :
    (fun z => v⁻¹*f z*v)∈polynomials H 0 := by
  have hv : (fun _ : ℤ => v)∈polynomials H 0 := const_mem (by rw [h0]; trivial)
  exact (polynomials H 0).mul_mem ((polynomials H 0).mul_mem ((polynomials H 0).inv_mem hv) hf) hv

lemma affine_conjugate_polynomial (H : Filtration G) (h0 : H.level 0=⊤)
    {f : ℤ → G} (hf : f∈polynomials H 0) (a b : ℤ) (v : G) :
    (fun z => v⁻¹*f (a*z+b)*v)∈polynomials H 0 :=
  conjugate_polynomial H h0 (affine_polynomial H hf a b) v

lemma factor_coset (Γ : Subgroup G) (e f b v : G)
    (hv : (QuotientGroup.mk b : G⧸Γ)=QuotientGroup.mk v) :
    (QuotientGroup.mk (e*f*b) : G⧸Γ) = (e*v) • QuotientGroup.mk (v⁻¹*f*v) := by
  calc
    _ = (e*f) • (QuotientGroup.mk b : G⧸Γ) := rfl
    _ = (e*f) • QuotientGroup.mk v := by rw [hv]
    _ = QuotientGroup.mk ((e*f)*v) := rfl
    _ = QuotientGroup.mk ((e*v)*(v⁻¹*f*v)) := by congr 1; group
    _ = _ := rfl

 

theorem periodic_factor_coset (Γ : Subgroup G) (f e f' b : ℤ → G)
    (he : ∀ z, f z=e z*f' z*b z) (T : ℤ)
    (hper : Function.Periodic (fun z => (QuotientGroup.mk (b z) : G⧸Γ)) T)
    (r : ℤ) (v : G) (hv : (QuotientGroup.mk (b r) : G⧸Γ)=QuotientGroup.mk v) (z : ℤ) :
    (QuotientGroup.mk (f (T*z+r)) : G⧸Γ) =
      (e (T*z+r)*v) • QuotientGroup.mk (v⁻¹*f' (T*z+r)*v) := by
  rw [he]
  apply factor_coset
  have hh := (hper.int_mul z) r
  have hi : T*z+r=r+z*T := by ring
  rw [hi]
  have hh' : (QuotientGroup.mk (b (r+z*T)) : G⧸Γ)=QuotientGroup.mk (b r) := by simpa using hh
  exact hh'.trans hv

end FactorProgression
end
end
 

 
section
noncomputable section
open scoped Topology
namespace CompactActionFreeze
variable {G V X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [MetricSpace X] [CompactSpace X]
  [MulAction G X] [ContinuousSMul G X]

 

omit [IsTopologicalGroup G] in
theorem small_displacement [IsTopologicalGroup G] (c : G ≃ₜ V) (hc : c 1=0) (ε : ℝ) (hε : 0<ε) :
    ∃ u : ℝ, 0<u ∧ ∀ g : G, ‖c g‖ ≤ u → ∀ x : X, dist (g • x) x ≤ ε := by
  let F : C(V × X,ℝ) := ⟨fun p => dist (c.symm p.1 • p.2) p.2,by fun_prop⟩
  let A : C(V,C(X,ℝ)) := F.curry
  have hA0 : A 0=0 := by
    ext x
    have he : c.symm 0=1 := by rw [← hc,c.symm_apply_apply]
    simp [A,F,ContinuousMap.curry_apply,he]
  obtain ⟨u,hu,hs⟩ := Metric.continuousAt_iff.mp A.continuous.continuousAt ε hε
  refine ⟨u/2,by positivity,fun g hg x => ?_⟩
  have hd : dist (c g) 0<u := by simpa only [dist_zero_right] using (show ‖c g‖<u by linarith)
  have hh := hs hd
  rw [hA0,dist_zero_right] at hh
  have hx := (A (c g)).norm_coe_le_norm x
  have hv : (A (c g)) x=dist (g • x) x := by simp [A,F,ContinuousMap.curry_apply]
  rw [hv,Real.norm_eq_abs,abs_of_nonneg dist_nonneg] at hx
  exact (hx.trans_lt hh).le

end CompactActionFreeze
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace ProgressionPartition
lemma sum_blocks {M : Type*} [AddCommMonoid M] (f : ℕ → M) (A B : ℕ) :
    (∑ i ∈ Finset.range (A*B), f i) =
      ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B, f (a*B+b) := by
  induction A with
  | zero => simp
  | succ A ih =>
    rw [Nat.succ_mul,Finset.sum_range_add,ih,Finset.sum_range_succ]

lemma sum_progressions {M : Type*} [AddCommMonoid M] (f : ℕ → M) (J K T : ℕ) :
    (∑ i ∈ Finset.range (J*K*T), f i) =
      ∑ a ∈ Finset.range J, ∑ r ∈ Finset.range T,
        ∑ n ∈ Finset.range K, f ((a*K+n)*T+r) := by
  rw [sum_blocks f (J*K) T,sum_blocks (fun i => ∑ r ∈ Finset.range T, f (i*T+r)) J K]
  apply Finset.sum_congr rfl
  intro a ha
  exact Finset.sum_comm

lemma residual_bound (f : ℕ → ℂ) (μ : ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) (hμ : ‖μ‖ ≤ 1)
    (A B : ℕ) :
    ‖∑ i ∈ Finset.range (A+B), (f i-μ)‖ ≤
      ‖∑ i ∈ Finset.range A, (f i-μ)‖+2*B := by
  rw [Finset.sum_range_add]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  calc
    _ ≤ ∑ i ∈ Finset.range B, ‖f (A+i)-μ‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range B, (2:ℝ) := Finset.sum_le_sum (fun i _ =>
      (norm_sub_le _ _).trans (by linarith [hf (A+i)]))
    _ = _ := by simp; ring

 

theorem obstruction (f : ℕ → ℂ) (g : ℕ → ℕ → ℕ → ℂ) (μ : ℂ)
    (J K T N : ℕ) (δ : ℝ) (hδ : 0<δ) (hN : 0<N)
    (hM : J*K*T ≤ N) (hf : ∀ i, ‖f i‖ ≤ 1) (hμ : ‖μ‖ ≤ 1)
    (htail : 2*((N-J*K*T:ℕ):ℝ) ≤ δ*N/4)
    (hfreeze : ∀ a<J, ∀ r<T, ∀ n<K,
      ‖f ((a*K+n)*T+r)-g a r n‖ ≤ δ/4)
    (hlarge : δ*N ≤ ‖∑ i ∈ Finset.range N, (f i-μ)‖) :
    ∃ a<J, ∃ r<T, δ/4*K ≤ ‖∑ n ∈ Finset.range K, (g a r n-μ)‖ := by
  by_contra hno
  push Not at hno
  have hcell (a : ℕ) (ha : a<J) (r : ℕ) (hr : r<T) :
      ‖∑ n ∈ Finset.range K, (f ((a*K+n)*T+r)-μ)‖ ≤ δ/2*K := by
    have he : (∑ n ∈ Finset.range K, (f ((a*K+n)*T+r)-μ)) =
        (∑ n ∈ Finset.range K, (f ((a*K+n)*T+r)-g a r n))+
        ∑ n ∈ Finset.range K, (g a r n-μ) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    rw [he]
    calc
      _ ≤ ‖∑ n ∈ Finset.range K, (f ((a*K+n)*T+r)-g a r n)‖+
          ‖∑ n ∈ Finset.range K, (g a r n-μ)‖ := norm_add_le _ _
      _ ≤ (∑ n ∈ Finset.range K, δ/4)+δ/4*K := by
        apply add_le_add
        · exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n hn => hfreeze a ha r hr n (Finset.mem_range.mp hn)))
        · exact (hno a ha r hr).le
      _ = _ := by simp; ring
  have hblock : ‖∑ i ∈ Finset.range (J*K*T), (f i-μ)‖ ≤ δ/2*(J*K*T:ℕ) := by
    rw [sum_progressions]
    calc
      _ ≤ ∑ a ∈ Finset.range J, ‖∑ r ∈ Finset.range T,
          ∑ n ∈ Finset.range K, (f ((a*K+n)*T+r)-μ)‖ := norm_sum_le _ _
      _ ≤ ∑ a ∈ Finset.range J, ∑ r ∈ Finset.range T, δ/2*K := by
        apply Finset.sum_le_sum
        intro a ha
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r hr => hcell a (Finset.mem_range.mp ha) r (Finset.mem_range.mp hr)))
      _ = _ := by simp; ring
  have hres := residual_bound f μ hf hμ (J*K*T) (N-J*K*T)
  rw [Nat.add_sub_of_le hM] at hres
  have hm : (J*K*T:ℕ) ≤ (N:ℝ) := by exact_mod_cast hM
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hmδ := mul_le_mul_of_nonneg_left hm (show 0 ≤ δ/2 by positivity)
  have hp : 0<δ*(N:ℝ) := mul_pos hδ hn
  linarith

end ProgressionPartition
end
end
 

 
section
noncomputable section
namespace ProgressionPartition
lemma radix_lt {a A b B : ℕ} (ha : a<A) (hb : b<B) : a*B+b<A*B := by
  calc
    _ < a*B+B := Nat.add_lt_add_left hb _
    _ = (a+1)*B := by ring
    _ ≤ A*B := Nat.mul_le_mul_right B (by omega)

lemma cell_lt {J K T a n r : ℕ} (ha : a<J) (hn : n<K) (hr : r<T) :
    (a*K+n)*T+r<J*K*T := radix_lt (radix_lt ha hn) hr

 

theorem uniform_scales (J Tmax : ℕ) (hJ : 0<J) (hTmax : 0<Tmax)
    (δ : ℝ) (hδ : 0<δ) :
    ∃ N₀ : ℕ, 0<N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ T : ℕ, 0<T → T ≤ Tmax →
      let K := N/(J*T)
      0<K ∧ J*K*T ≤ N ∧ N ≤ 2*J*Tmax*K ∧
      2*((N-J*K*T:ℕ):ℝ) ≤ δ*N/4 := by
  obtain ⟨N₀,hN₀⟩ := exists_nat_gt (max ((J*Tmax:ℕ):ℝ) (8*(J*Tmax:ℕ)/δ))
  have h₀ : (J*Tmax:ℕ)<(N₀:ℝ) := lt_of_le_of_lt (le_max_left _ _) hN₀
  have h₁ : 8*(J*Tmax:ℕ)/δ<(N₀:ℝ) := lt_of_le_of_lt (le_max_right _ _) hN₀
  have hn₀ : 0<N₀ := by exact_mod_cast (lt_of_le_of_lt (by positivity : (0:ℝ) ≤ (J*Tmax:ℕ)) h₀)
  refine ⟨N₀,hn₀,fun N hN T hT hTT => ?_⟩
  dsimp only
  have hd : 0<J*T := Nat.mul_pos hJ hT
  have hJN : J*T ≤ N := by
    have hJNm : J*Tmax<N₀ := by exact_mod_cast h₀
    exact (Nat.mul_le_mul_left J hTT).trans (Nat.le_of_lt hJNm |>.trans hN)
  have hK : 0<N/(J*T) := Nat.div_pos hJN hd
  have hM : J*(N/(J*T))*T ≤ N := by
    simpa only [Nat.mul_assoc,Nat.mul_left_comm (N/(J*T)),Nat.mul_comm T] using Nat.div_mul_le_self N (J*T)
  have hmod := Nat.mod_lt N hd
  have hid := Nat.mod_add_div N (J*T)
  have hremainder : N-J*(N/(J*T))*T < J*T := by
    have he : J*(N/(J*T))*T=(J*T)*(N/(J*T)) := by ring
    rw [he]
    omega
  refine ⟨hK,hM,?_,?_⟩
  · have hsmall : J*T ≤ J*T*(N/(J*T)) := Nat.le_mul_of_pos_right _ hK
    have hstep : N ≤ 2*J*T*(N/(J*T)) := by nlinarith only [hid,hmod,hsmall]
    exact hstep.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left (2*J) hTT))
  · have he : 8*(J*Tmax:ℕ)/δ ≤ (N:ℝ) := h₁.le.trans (by exact_mod_cast hN)
    have hh : 8*(J*Tmax:ℕ) ≤ (N:ℝ)*δ := (div_le_iff₀ hδ).mp he
    have hr : ((N-J*(N/(J*T))*T:ℕ):ℝ) ≤ (J*Tmax:ℕ) := by
      exact_mod_cast (hremainder.le.trans (Nat.mul_le_mul_left J hTT))
    linarith

end ProgressionPartition
end

end
end
end
end

end OAI
