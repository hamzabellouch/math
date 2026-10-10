import OAI.Analysis.DiamondDistortion.StartModels

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace CoordinateCompletion.Data
variable {ι κ : Type*} (A : CoordinateCompletion.Data ι)
abbrev Dual := StrongDual ℝ A.Space

def dualEmbedding : (ι →₀ ℝ) →ₗ[ℝ] A.Dual :=
  Finsupp.linearCombination ℝ A.coordinate
lemma dualEmbedding_apply (v : ι →₀ ℝ) (x : A.Space) :
    A.dualEmbedding v x=∑ i ∈ v.support,v i*A.coordinate i x := by
  simp only [dualEmbedding,Finsupp.linearCombination_apply,Finsupp.sum,
    sum_apply,smul_apply,smul_eq_mul]
lemma dualEmbedding_embedding (v w : ι →₀ ℝ) :
    A.dualEmbedding v (A.embedding w)=∑ i ∈ v.support,v i*w i := by
  rw [A.dualEmbedding_apply]
  simp only [coordinate_embedding]

def dualProjection (S : Finset ι) : A.Dual →L[ℝ] A.Dual :=
  ∑ i ∈ S,(ContinuousLinearMap.apply ℝ ℝ (A.unit i)).smulRight (A.coordinate i)
lemma dualProjection_apply (S : Finset ι) (x : A.Dual) :
    A.dualProjection S x=∑ i ∈ S,x (A.unit i) • A.coordinate i := by simp [dualProjection]
lemma dualProjection_unit (S : Finset ι) (x : A.Dual) (i : ι) :
    A.dualProjection S x (A.unit i)=if i ∈ S then x (A.unit i) else 0 := by
  rw [dualProjection_apply]
  simp [coordinate_unit,mul_ite]
lemma dualProjection_idempotent (S : Finset ι) (x : A.Dual) :
    A.dualProjection S (A.dualProjection S x)=A.dualProjection S x := by
  rw [dualProjection_apply]
  simp only [dualProjection_unit]
  rw [dualProjection_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ite_eq_left hi]
lemma dualProjection_fixed (v : ι →₀ ℝ) {S : Finset ι} (hS : v.support ⊆ S) :
    A.dualProjection S (A.dualEmbedding v)=A.dualEmbedding v := by
  have hev (i : ι) : A.dualEmbedding v (A.unit i)=v i := by
    rw [unit,dualEmbedding_embedding]
    simp [Finsupp.single_apply,mul_ite]
    exact fun h => h.symm
  rw [dualProjection_apply]
  simp only [hev]
  change (∑ i ∈ S,v i • A.coordinate i)=∑ i ∈ v.support,v i • A.coordinate i
  exact Eq.symm (Finset.sum_subset hS (by intro i _ hi; rw [Finsupp.notMem_support_iff.mp hi,zero_smul]))

def dualHeadMap (S : Finset ι) : (S → ℝ) →ₗ[ℝ] A.Dual where
  toFun a := ∑ i : S,a i • A.coordinate i
  map_add' a b := by simp [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' t a := by simp [Pi.smul_apply,smul_smul,Finset.smul_sum]
lemma dualProjection_finite (S : Finset ι) :
    FiniteDimensional ℝ (LinearMap.range (A.dualProjection S).toLinearMap) := by
  have hle : LinearMap.range (A.dualProjection S).toLinearMap ≤ LinearMap.range (A.dualHeadMap S) := by
    rintro x ⟨y,rfl⟩
    refine ⟨fun i => y (A.unit i),?_⟩
    change (∑ i : S,y (A.unit i) • A.coordinate i)=A.dualProjection S y
    rw [dualProjection_apply]
    exact Finset.sum_attach S (fun i => y (A.unit i) • A.coordinate i)
  let : FiniteDimensional ℝ (LinearMap.range (A.dualHeadMap S)) := Module.Finite.range _
  exact Submodule.finiteDimensional_of_le hle

lemma embedding_sum (v : ι →₀ ℝ) : A.embedding v=∑ i ∈ v.support,v i • A.unit i := by
  simp only [unit,← map_smul,← map_sum]
  congr 1
  ext i
  simp [Finsupp.single_apply,Finset.sum_ite_eq']
lemma pairing (x : A.Dual) (v : ι →₀ ℝ) :
    x (A.embedding v)=∑ i ∈ v.support,v i*x (A.unit i) := by
  rw [embedding_sum,map_sum]
  simp only [map_smul,smul_eq_mul]

lemma small_color_tail_upper (c : ι → κ)
    (hblock : ∀ p q : ι →₀ ℝ,Disjoint (p.support.image c) (q.support.image c) →
      (A.seminorm (p+q))^2 ≤ (A.seminorm p)^2+(A.seminorm q)^2)
    (x : A.Dual) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Finset κ, ∀ p : ι →₀ ℝ, (∀ v ∈ p.support, c v ∉ C) →
      x (A.embedding p) ≤ ε*A.seminorm p := by
  classical
  by_contra hn
  push Not at hn
  have hchoose (C : Finset κ) : ∃ q : ι →₀ ℝ,
      (∀ v ∈ q.support,c v ∉ C) ∧ A.seminorm q=1 ∧ ε < x (A.embedding q) := by
    obtain ⟨p,hout,hval⟩ := hn C
    have hpn0 : A.seminorm p ≠ 0 := by
      intro he
      have hp0 := A.separates p he
      simp only [hp0,map_zero,mul_zero,lt_self_iff_false] at hval
    have hpn : 0 < A.seminorm p := lt_of_le_of_ne (apply_nonneg _ _) hpn0.symm
    let q := (A.seminorm p)⁻¹ • p
    refine ⟨q, ?_, ?_, ?_⟩
    · intro v hv
      apply hout v
      apply Finsupp.mem_support_iff.mpr
      intro hpv
      have hqv : q v=0 := by simp [q,Finsupp.smul_apply,hpv]
      exact (Finsupp.mem_support_iff.mp hv) hqv
    · simp only [q,map_smul_eq_mul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpn)]
      exact inv_mul_cancel₀ hpn0
    · simp only [q,map_smul,smul_eq_mul]
      rw [inv_mul_eq_div]
      exact (lt_div_iff₀ hpn).mpr hval
  have hblocks : ∀ n : ℕ, ∃ p : ι →₀ ℝ,
      (A.seminorm p)^2 ≤ (n : ℝ) ∧ (n : ℝ)*ε ≤ x (A.embedding p) := by
    intro n
    induction n with
    | zero => exact ⟨0,by simp only [map_zero,zero_pow (by decide : 2 ≠ 0),Nat.cast_zero,le_refl],
        by simp only [map_zero,Nat.cast_zero,zero_mul,le_refl]⟩
    | succ n ih =>
      obtain ⟨p,hpn,hpx⟩ := ih
      obtain ⟨q,hqout,hqn,hqx⟩ := hchoose (p.support.image c)
      have hd : Disjoint (p.support.image c) (q.support.image c) := by
        apply Finset.disjoint_left.mpr
        intro a hap haq
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp haq
        exact hqout v hv hap
      refine ⟨p+q, ?_, ?_⟩
      · have h := hblock p q hd
        rw [hqn] at h
        push_cast
        nlinarith
      · simp only [map_add,Nat.cast_add,Nat.cast_one]
        nlinarith
  obtain ⟨n,hn⟩ := exists_nat_gt (‖x‖^2/ε^2)
  have hn0 : (0:ℝ) < n := lt_of_le_of_lt (div_nonneg (sq_nonneg _) (sq_nonneg _)) hn
  have hnε : ‖x‖^2 < (n:ℝ)*ε^2 := (div_lt_iff₀ (sq_pos_of_pos hε)).mp hn
  obtain ⟨p,hpn,hpx⟩ := hblocks n
  have hxb : x (A.embedding p) ≤ ‖x‖*A.seminorm p := by
    calc
      _ ≤ ‖x (A.embedding p)‖ := Real.le_norm_self _
      _ ≤ ‖x‖*‖A.embedding p‖ := x.le_opNorm _
      _ = _ := by rw [A.norm_embedding]
  have hprod : (n:ℝ)*ε ≤ ‖x‖*A.seminorm p := hpx.trans hxb
  have hsquare := (sq_le_sq₀ (mul_nonneg hn0.le hε.le)
    (mul_nonneg (norm_nonneg _) (apply_nonneg _ _))).2 hprod
  have hmul := mul_le_mul_of_nonneg_left hpn (sq_nonneg ‖x‖)
  have hcontra := mul_pos hn0 (sub_pos.mpr hnε)
  nlinarith

lemma small_color_tail (c : ι → κ)
    (hblock : ∀ p q : ι →₀ ℝ,Disjoint (p.support.image c) (q.support.image c) →
      (A.seminorm (p+q))^2 ≤ (A.seminorm p)^2+(A.seminorm q)^2)
    (x : A.Dual) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Finset κ, ∀ p : ι →₀ ℝ, (∀ v ∈ p.support, c v ∉ C) →
      |x (A.embedding p)| ≤ ε*A.seminorm p := by
  obtain ⟨C,hC⟩ := A.small_color_tail_upper c hblock x hε
  refine ⟨C,?_⟩
  intro p hp
  apply abs_le.mpr
  refine ⟨?_,hC p hp⟩
  have h := hC (-p) (by simpa only [Finsupp.support_neg] using hp)
  simp only [map_neg,map_neg_eq_map] at h
  linarith

/-- Orthogonal outer blocks whose finite unions have their actual norm equivalent
    to coordinate ℓ². Constants may depend on the finite union, not globally. -/
structure HilbertBlocks (c : ι → κ) : Prop where
  orthogonal : ∀ p q : ι →₀ ℝ,Disjoint (p.support.image c) (q.support.image c) →
    (A.seminorm (p+q))^2 ≤ (A.seminorm p)^2+(A.seminorm q)^2
  contractive : ∀ p : ι →₀ ℝ,∀ C : Set κ,
    A.seminorm (p.filter (fun i => c i ∈ C)) ≤ A.seminorm p
  upper : ∀ C : Finset κ,∃ B : ℝ,0 < B ∧ ∀ p : ι →₀ ℝ,
    (∀ i ∈ p.support,c i ∈ C) →
    (A.seminorm p)^2 ≤ B*(∑ i ∈ p.support,p i^2)
  lower : ∀ C : Finset κ,∃ L : ℝ,0 < L ∧ ∀ p : ι →₀ ℝ,
    (∀ i ∈ p.support,c i ∈ C) →
    (∑ i ∈ p.support,p i^2) ≤ L*(A.seminorm p)^2

end CoordinateCompletion.Data

namespace FiniteCoordinates
variable {ι : Type*}
def array (S : Finset ι) (a : ι → ℝ) : ι →₀ ℝ := ∑ i ∈ S,a i • Finsupp.single i 1
lemma array_apply (S : Finset ι) (a : ι → ℝ) (i : ι) :
    array S a i=if i ∈ S then a i else 0 := by
  simp [array,Finsupp.single_apply,Finset.sum_ite_eq']
lemma array_support (S : Finset ι) (a : ι → ℝ) : (array S a).support ⊆ S := by
  intro i hi
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hi) (by rw [array_apply,ite_eq_right hn])
lemma array_energy (S : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ (array S a).support,array S a i^2)=∑ i ∈ S,a i^2 := by
  calc
    _ = ∑ i ∈ S,array S a i^2 := by
      apply Finset.sum_subset (array_support S a)
      intro i _ hi
      rw [Finsupp.notMem_support_iff.mp hi]
      norm_num
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [array_apply,ite_eq_left hi]
lemma filter_energy_le (p : ι →₀ ℝ) (Q : ι → Prop) [DecidablePred Q] :
    (∑ i ∈ (p.filter Q).support,(p.filter Q) i^2) ≤ ∑ i ∈ p.support,p i^2 := by
  rw [Finsupp.support_filter]
  calc
    _ = ∑ i ∈ p.support.filter Q,p i^2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finsupp.filter_apply,ite_eq_left (Finset.mem_filter.mp hi).2]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
lemma square_tails (a : ι → ℝ) {M : ℝ}
    (hM : ∀ S : Finset ι,(∑ i ∈ S,a i^2) ≤ M) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : Finset ι,∀ U : Finset ι,Disjoint S U → (∑ i ∈ U,a i^2) < δ := by
  let E : Set ℝ := Set.range (fun S : Finset ι => ∑ i ∈ S,a i^2)
  have hEb : BddAbove E := ⟨M,by rintro _ ⟨S,rfl⟩; exact hM S⟩
  have hEn : E.Nonempty := ⟨0,∅,by simp⟩
  obtain ⟨b,⟨S,rfl⟩,hS⟩ := exists_lt_of_lt_csSup hEn (sub_lt_self (sSup E) hδ)
  refine ⟨S,?_⟩
  intro U hU
  have h := le_csSup hEb (show (∑ i ∈ S ∪ U,a i^2) ∈ E from ⟨S ∪ U,rfl⟩)
  rw [Finset.sum_union hU] at h
  linarith
end FiniteCoordinates

namespace CoordinateCompletion.Data
variable {ι κ : Type*} (A : CoordinateCompletion.Data ι)
lemma pairing_array (S : Finset ι) (a : ι → ℝ) (x : A.Dual) :
    x (A.embedding (FiniteCoordinates.array S a))=∑ i ∈ S,a i*x (A.unit i) := by
  simp only [FiniteCoordinates.array,map_sum,map_smul,smul_eq_mul,unit]
lemma dualEmbedding_array (S : Finset ι) (a : ι → ℝ) (p : ι →₀ ℝ) :
    A.dualEmbedding (FiniteCoordinates.array S a) (A.embedding p)=∑ i ∈ S,a i*p i := by
  simp only [FiniteCoordinates.array,map_sum,map_smul]
  change (∑ i ∈ S,a i • A.dualEmbedding (Finsupp.single i 1)) (A.embedding p)=_
  simp only [dualEmbedding,Finsupp.linearCombination_single,one_smul,
    sum_apply,smul_apply,smul_eq_mul,coordinate_embedding]

def coefficients (c : ι → κ) (C : Finset κ) (x : A.Dual) (i : ι) : ℝ :=
  if c i ∈ C then x (A.unit i) else 0
lemma coefficients_bounded (c : ι → κ) (hblocks : A.HilbertBlocks c) (C : Finset κ) (x : A.Dual) :
    ∃ M : ℝ,∀ S : Finset ι,(∑ i ∈ S,A.coefficients c C x i^2) ≤ M := by
  obtain ⟨B,hB,hupper⟩ := hblocks.upper C
  refine ⟨B*‖x‖^2,?_⟩
  intro S
  let a := A.coefficients c C x
  let p := FiniteCoordinates.array S a
  let E := ∑ i ∈ S,a i^2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp : ∀ i ∈ p.support,c i ∈ C := by
    intro i hi
    by_contra hn
    have he : a i=0 := ite_eq_right hn
    have hh : p i=0 := by rw [FiniteCoordinates.array_apply,he]; split_ifs <;> rfl
    exact (Finsupp.mem_support_iff.mp hi) hh
  have hpn := hupper p hp
  rw [FiniteCoordinates.array_energy] at hpn
  have he : x (A.embedding p)=E := by
    rw [pairing_array]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [a,coefficients]
    split_ifs <;> ring
  have hval : E ≤ ‖x‖*A.seminorm p := by
    rw [← he]
    exact (Real.le_norm_self _).trans (by simpa only [norm_embedding] using x.le_opNorm (A.embedding p))
  have hs := (sq_le_sq₀ hE (by positivity : 0 ≤ ‖x‖*A.seminorm p)).mpr hval
  have hm := mul_le_mul_of_nonneg_left hpn (sq_nonneg ‖x‖)
  change E ≤ B*‖x‖^2
  by_contra hn
  have hpos : 0 < E := lt_of_le_of_lt (by positivity) (lt_of_not_ge hn)
  have hc := mul_pos hpos (sub_pos.mpr (lt_of_not_ge hn))
  change (A.seminorm p)^2 ≤ B*E at hpn
  change ‖x‖^2*(A.seminorm p)^2 ≤ ‖x‖^2*(B*E) at hm
  nlinarith only [hs,hm,hc]

lemma dual_approximation (c : ι → κ) (hblocks : A.HilbertBlocks c)
    (x : A.Dual) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ι →₀ ℝ,‖x-A.dualEmbedding v‖ < ε := by
  have hε4 : 0 < ε/4 := by positivity
  obtain ⟨C,hC⟩ := A.small_color_tail c hblocks.orthogonal x hε4
  obtain ⟨L,hL,hlower⟩ := hblocks.lower C
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  let t := ε/(4*Real.sqrt L)
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨M,hM⟩ := A.coefficients_bounded c hblocks C x
  obtain ⟨S,hS⟩ := FiniteCoordinates.square_tails (A.coefficients c C x) hM (sq_pos_of_pos ht)
  let H := S.filter (fun i => c i ∈ C)
  let v := FiniteCoordinates.array H (fun i => x (A.unit i))
  refine ⟨v,?_⟩
  have hbound : ‖x-A.dualEmbedding v‖ ≤ ε/2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro z
    induction z using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih z =>
      let p := A.array z
      let pc := p.filter (fun i => c i ∈ C)
      let qi := pc.filter (fun i => i ∉ S)
      let qo := p.filter (fun i => c i ∉ C)
      let qh := p.filter (fun i => i ∈ H)
      have hiC : ∀ i ∈ qi.support,c i ∈ C := by
        intro i hi
        rw [Finsupp.support_filter] at hi
        have hh := (Finset.mem_filter.mp hi).1
        rw [Finsupp.support_filter] at hh
        exact (Finset.mem_filter.mp hh).2
      have hiS : Disjoint S qi.support := by
        apply Finset.disjoint_left.mpr
        intro i hi hqi
        rw [Finsupp.support_filter] at hqi
        exact (Finset.mem_filter.mp hqi).2 hi
      have hout : ∀ i ∈ qo.support,c i ∉ C := by
        intro i hi
        rw [Finsupp.support_filter] at hi
        exact (Finset.mem_filter.mp hi).2
      have hpc : A.seminorm pc ≤ A.seminorm p := by
        simpa only [pc,Finset.mem_coe] using hblocks.contractive p (C : Set κ)
      have hpn : 0 ≤ A.seminorm p := apply_nonneg _ _
      have hpcl := hlower pc (by
        intro i hi
        rw [Finsupp.support_filter] at hi
        exact (Finset.mem_filter.mp hi).2)
      have henergy : (∑ i ∈ qi.support,qi i^2) ≤ L*(A.seminorm p)^2 := by
        simpa only [qi] using (FiniteCoordinates.filter_energy_le pc (fun i => i ∉ S)).trans
          (hpcl.trans (mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (apply_nonneg _ _) hpn).mpr hpc) hL.le))
      have hroot : Real.sqrt (∑ i ∈ qi.support,qi i^2) ≤ Real.sqrt L*A.seminorm p := by
        apply (Real.sqrt_le_iff).mpr
        refine ⟨by positivity,?_⟩
        rw [mul_pow,Real.sq_sqrt hL.le]
        exact henergy
      have htail : Real.sqrt (∑ i ∈ qi.support,A.coefficients c C x i^2) ≤ t :=
        (Real.sqrt_le_left ht.le).mpr (hS qi.support hiS).le
      have hei : x (A.embedding qi)=∑ i ∈ qi.support,qi i*A.coefficients c C x i := by
        rw [pairing]
        apply Finset.sum_congr rfl
        intro i hi
        rw [coefficients,ite_eq_left (hiC i hi)]
      have hival : |x (A.embedding qi)| ≤ (ε/4)*A.seminorm p := by
        rw [hei]
        calc
          _ ≤ ∑ i ∈ qi.support,|qi i| * |A.coefficients c C x i| := by
            simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
              (fun i => qi i*A.coefficients c C x i) qi.support
          _ ≤ Real.sqrt (∑ i ∈ qi.support,qi i^2)*Real.sqrt (∑ i ∈ qi.support,A.coefficients c C x i^2) := by
            simpa only [sq_abs] using Real.sum_mul_le_sqrt_mul_sqrt qi.support
              (fun i => |qi i|) (fun i => |A.coefficients c C x i|)
          _ ≤ (Real.sqrt L*A.seminorm p)*t := mul_le_mul hroot htail (Real.sqrt_nonneg _) (by positivity)
          _ = _ := by dsimp [t]; field_simp [ne_of_gt hsL]
      have hoval : |x (A.embedding qo)| ≤ (ε/4)*A.seminorm p := by
        have hh : A.seminorm qo ≤ A.seminorm p := by
          convert hblocks.contractive p {a | a ∉ C} using 1
          congr 1
          ext i
          simp [qo,Finsupp.filter_apply]
        exact (hC qo hout).trans (mul_le_mul_of_nonneg_left hh hε4.le)
      have hsum : qh+qi+qo=p := by
        ext i
        by_cases hc : c i ∈ C <;> by_cases hs : i ∈ S <;>
          simp [qh,qi,qo,pc,H,hc,hs]
      have hv : A.dualEmbedding v (A.embedding p)=x (A.embedding qh) := by
        rw [dualEmbedding_array]
        have hqh : qh=FiniteCoordinates.array H (fun i => p i) := by
          ext i
          simp [qh,Finsupp.filter_apply,FiniteCoordinates.array_apply]
        rw [hqh,pairing_array]
        apply Finset.sum_congr rfl
        intro i _
        ring
      have hd : (x-A.dualEmbedding v) (A.embedding p)=x (A.embedding qi)+x (A.embedding qo) := by
        change x (A.embedding p)-A.dualEmbedding v (A.embedding p)=_
        rw [hv,← hsum,map_add,map_add,map_add,map_add]
        ring
      rw [UniformSpace.Completion.norm_coe]
      change ‖(x-A.dualEmbedding v) (A.embedding p)‖ ≤ (ε/2)*A.seminorm p
      rw [hd,Real.norm_eq_abs]
      exact (abs_add_le _ _).trans ((add_le_add hival hoval).trans_eq (by ring))
  exact hbound.trans_lt (by linarith)

lemma dual_separable [Countable ι] (c : ι → κ) (hblocks : A.HilbertBlocks c) :
    TopologicalSpace.SeparableSpace A.Dual := by
  let V := Submodule.span ℝ (Set.range A.coordinate)
  have hdense : Dense (V : Set A.Dual) := by
    intro x
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨v,hv⟩ := A.dual_approximation c hblocks x hε
    refine ⟨A.dualEmbedding v,?_,?_⟩
    · change (∑ i ∈ v.support,v i • A.coordinate i) ∈ V
      exact Submodule.sum_mem V (fun i _ => V.smul_mem _ (Submodule.subset_span ⟨i,rfl⟩))
    · simpa only [dist_eq_norm] using hv
  apply hdense.isSeparable_iff.mp
  exact (Set.countable_range A.coordinate).isSeparable.span

lemma dualProjection_commutes (S T : Finset ι) (x : A.Dual) :
    A.dualProjection S (A.dualProjection T x)=A.dualProjection T (A.dualProjection S x) := by
  rw [A.dualProjection_apply S (A.dualProjection T x),
    A.dualProjection_apply T (A.dualProjection S x)]
  simp only [dualProjection_unit,ite_smul,zero_smul]
  rw [← Finset.sum_filter,← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter,and_comm]

end CoordinateCompletion.Data

end DiamondDistortion

end

end OAI
