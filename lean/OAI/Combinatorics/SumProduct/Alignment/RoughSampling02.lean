import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.FinitePiece01
import OAI.Combinatorics.SumProduct.Alignment.UniformSlow01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
noncomputable section
open scoped BigOperators NNReal
end
 
end

section
 

 

noncomputable section
open scoped BigOperators NNReal
namespace RoughKernelFactorization
open RationalLattice MalcevCharacters FinitePieceAverages
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G (n+1)) (hsk : SecondKind c)
variable (χ : G →* Multiplicative ℝ) (Γ : Subgroup G)
variable (R : Reduction c hsk χ Γ)
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
variable (hcont : Continuous χ) (hZ : ∀ g∈Γ,∃ z : ℤ,(χ g).toAdd=z)
variable {X : Type*} [PseudoMetricSpace X] (v : (G⧸Γ) ≃ₜ X)

def residueSigma (j : Fin R.period) : G:=
  R.flow c hsk χ Γ (Multiplicative.ofAdd (j.val:ℝ))

include hΓ hcont hZ in
 

theorem finite_residue_kernel_reduction (T : ℝ) (K : ℝ≥0) (B : ℝ) (hB : 0≤B)
    (ε : ℝ) (hε : 0<ε) :
    ∃ L : ℝ≥0,∀ (V α : Type*) [DecidableEq α] (m : MvPolynomial V ℤ) (u : V → ℤ),
    ∃ j : Fin R.period,
    let σ:=residueSigma c hsk χ Γ R j
    letI :=kernelCompatibleMetric χ Γ σ c hsk R hΓ hcont hZ
    ∀ (a : Set.Icc (-T) T) (F : X → ℂ),LipschitzWith K F → (∀ x,‖F x‖≤B) →
    ∃ g : (χ.ker⧸kernelLattice χ Γ σ) → ℂ,LipschitzWith L g ∧ (∀ y,‖g y‖≤B+ε) ∧
    ∀ (S U : Finset α) (input : α → V → ℤ) (P : α → G) (Q : α → χ.ker),
    (∀ x∈S∪U,∀ i,Int.ModEq (R.period:ℤ) (input x i) (u i)) →
    (∀ x∈S∪U,P x=R.flow c hsk χ Γ (Multiplicative.ofAdd a.val)*
      (Q x).val*R.flow c hsk χ Γ
        (Multiplicative.ofAdd ((MvPolynomial.eval (input x) m:ℤ):ℝ))) →
    ∀ η : ℝ,η≤‖mean S (fun x=>F (v (QuotientGroup.mk (P x))))-
      mean U (fun x=>F (v (QuotientGroup.mk (P x))))‖ →
    η-2*ε≤‖mean S (fun x=>g (QuotientGroup.mk (Q x)))-
      mean U (fun x=>g (QuotientGroup.mk (Q x)))‖ := by
  obtain ⟨L,hL⟩:=uniform_finite_kernel_tests c hsk χ Γ R hΓ hcont hZ v
    (residueSigma c hsk χ Γ R) T K B hB ε hε
  refine ⟨L,?_⟩
  intro V α _ m u
  let r : ℤ:=MvPolynomial.eval u m % (R.period:ℤ)
  have hr:=residue_range c hsk χ Γ R m u
  let j : Fin R.period:=⟨r.toNat,by
    have he : (r.toNat:ℤ)=r:=Int.toNat_of_nonneg hr.1
    exact_mod_cast (show (r.toNat:ℤ)<R.period by rw [he]; exact hr.2)⟩
  have hj : (j.val:ℝ)=(r:ℝ):=by
    dsimp [j]
    exact_mod_cast (Int.toNat_of_nonneg hr.1)
  refine ⟨j,?_⟩
  dsimp only
  let σ:=residueSigma c hsk χ Γ R j
  let :=kernelCompatibleMetric χ Γ σ c hsk R hΓ hcont hZ
  intro a F hF hbound
  obtain ⟨g,hg,he,hgB⟩:=hL j a F hF hbound
  refine ⟨g,hg,hgB,?_⟩
  intro S U input P Q hres hP η hd
  let f : α → ℂ:=fun x=>F (v (QuotientGroup.mk (P x)))
  let f' : α → ℂ:=fun x=>g (QuotientGroup.mk (Q x))
  have hpoint : ∀ x∈S∪U,‖f x-f' x‖≤ε:=by
    intro x hx
    have hp:=factorization_on_residue c hsk χ Γ R m (input x) u (hres x hx)
      (P x) (R.flow c hsk χ Γ (Multiplicative.ofAdd a.val)) (Q x) (hP x hx)
    have hσ : σ=R.flow c hsk χ Γ (Multiplicative.ofAdd (r:ℝ)):=by
      dsimp only [σ,residueSigma]
      rw [hj]
    have hp' : (QuotientGroup.mk (P x) : G⧸Γ)=kernelTestMap χ Γ σ
        (R.flow c hsk χ Γ (Multiplicative.ofAdd a.val)) (QuotientGroup.mk (Q x)):=by
      rw [hσ]
      exact hp
    change ‖F (v (QuotientGroup.mk (P x)))-g (QuotientGroup.mk (Q x))‖≤ε
    rw [hp',norm_sub_rev]
    exact (he (QuotientGroup.mk (Q x))).le
  have hs : ‖mean S f-mean S f'‖≤ε:=mean_error S f f' ε hε.le
    (fun x hx=>hpoint x (Finset.mem_union_left U hx))
  have hu : ‖mean U f-mean U f'‖≤ε:=mean_error U f f' ε hε.le
    (fun x hx=>hpoint x (Finset.mem_union_right S hx))
  have h₁:=norm_sub_le (mean S f-mean S f') (mean U f-mean S f')
  have h₂:=norm_sub_le (mean U f-mean U f') (mean S f'-mean U f')
  have he₁ : (mean S f-mean S f')-(mean U f-mean S f')=mean S f-mean U f:=by ring
  have he₂ : (mean U f-mean U f')-(mean S f'-mean U f')=mean U f-mean S f':=by ring
  rw [he₁] at h₁
  rw [he₂] at h₂
  change η≤‖mean S f-mean U f‖ at hd
  change η-2*ε≤‖mean S f'-mean U f'‖
  linarith

end RoughKernelFactorization
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RoughSamplingWeights
open FinitePieceAverages
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rescaledEndpoint (v : ι → ℝ) (u : ι → ℤ) (K : ℕ) : ι → ℝ:=
  fun i=>(v i-u i)/K

def integerAffine (u : ι → ℤ) (K : ℕ) (y : ι → ℤ) : ι → ℤ:=
  fun i=>u i+(K:ℤ)*y i

lemma rescaled_box (lo hi : ι → ℝ) (u : ι → ℤ) (K : ℕ) (hK : 0<K) :
    boxIndices lo hi (fun i=>(u i:ℝ)) K=
      boxIndices (rescaledEndpoint lo u K) (rescaledEndpoint hi u K) (fun _=>0) 1 := by
  have hKr : 0<(K:ℝ):=by exact_mod_cast hK
  ext y
  rw [mem_boxIndices _ _ _ _ hKr,mem_boxIndices _ _ _ _ zero_lt_one]
  apply forall_congr'
  intro i
  simp only [rescaledEndpoint,zero_add,one_mul,div_le_iff₀ hKr,lt_div_iff₀ hKr]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> nlinarith

 

def physicalResidueBox (lo hi : ι → ℝ) (u : ι → ℤ) (K : ℕ) : Finset (ι → ℤ):=
  (boxIndices lo hi (fun _=>0) 1).filter (fun x=>∀ i,x i ≡ u i [ZMOD K])

lemma physical_residue_reparametrization (lo hi : ι → ℝ) (u : ι → ℤ)
    (K : ℕ) (hK : 0<K) :
    physicalResidueBox lo hi u K=
      (boxIndices (rescaledEndpoint lo u K) (rescaledEndpoint hi u K) (fun _=>0) 1).image
        (integerAffine u K) := by
  have he : physicalResidueBox lo hi u K=refinedSet lo hi (fun _=>0) 1 u K:=by
    ext x
    rw [physicalResidueBox,Finset.mem_filter,mem_boxIndices _ _ _ _ zero_lt_one,
      mem_refinedSet _ _ _ _ zero_lt_one _ _ hK]
    simp only [zero_add,one_mul]
    exact forall_and.symm
  rw [he,refinedSet]
  simp only [zero_add,one_mul]
  rw [rescaled_box lo hi u K hK]
  rfl

lemma mean_image {α β : Type*} [DecidableEq β] (s : Finset α) (e : α → β)
    (he : Function.Injective e) (f : β → ℂ) :
    mean (s.image e) f=mean s (fun x=>f (e x)) := by
  rw [mean,Finset.card_image_of_injective _ he,Finset.sum_image]
  · rfl
  · intro a _ b _ hab
    exact he hab

 
theorem residue_mean (lo hi : ι → ℝ) (u : ι → ℤ) (K : ℕ) (hK : 0<K)
    (f : (ι → ℤ) → ℂ) :
    mean (physicalResidueBox lo hi u K) f=
      mean (boxIndices (rescaledEndpoint lo u K) (rescaledEndpoint hi u K) (fun _=>0) 1)
        (fun y=>f (integerAffine u K y)) := by
  rw [physical_residue_reparametrization lo hi u K hK]
  exact mean_image _ _ (affine_injective u K hK) f

 

omit [Fintype ι] [DecidableEq ι] in
theorem residual_congruences (u a : ι → ℤ) (K t : ℕ) (h : K.Coprime t) :
    ∃ b : ι → ℤ,∀ y : ι → ℤ,
      (∀ i,integerAffine u K y i ≡ a i [ZMOD t]) ↔ ∀ i,y i ≡ b i [ZMOD t] := by
  choose b hb using fun i=>residue_parameter K t h (u i) (a i)
  exact ⟨b,fun y=>forall_congr' (fun i=>hb i (y i))⟩

 

theorem residual_mean (u a : ι → ℤ) (K t : ℕ) (hK : 0<K) (h : K.Coprime t) :
    ∃ b : ι → ℤ,∀ (lo hi : ι → ℝ) (f : (ι → ℤ) → ℂ),
      mean ((physicalResidueBox lo hi u K).filter (fun x=>∀ i,x i ≡ a i [ZMOD t])) f=
        mean ((boxIndices (rescaledEndpoint lo u K) (rescaledEndpoint hi u K) (fun _=>0) 1).filter
          (fun y=>∀ i,y i ≡ b i [ZMOD t])) (fun y=>f (integerAffine u K y)) := by
  classical
  obtain ⟨b,hb⟩:=residual_congruences u a K t h
  refine ⟨b,fun lo hi f=>?_⟩
  rw [physical_residue_reparametrization lo hi u K hK,Finset.filter_image]
  have hp : (fun y : ι → ℤ=>∀ i,integerAffine u K y i ≡ a i [ZMOD t])=
      (fun y : ι → ℤ=>∀ i,y i ≡ b i [ZMOD t]):=funext (fun y=>propext (hb y))
  simp only [hp]
  exact mean_image _ _ (affine_injective u K hK) f

 

omit [Fintype ι] [DecidableEq ι] in
theorem rescaled_geometry (lo hi : ι → ℝ) (u : ι → ℤ) (K : ℕ) (hK : 0<K)
    (Z C side : ℝ) (hZ : (K:ℝ)≤Z) (_hC : 0≤C)
    (hu : ∀ i,0≤u i ∧ u i≤K)
    (hb : ∀ i,-(C*Z)≤lo i ∧ hi i≤C*Z)
    (hs : ∀ i,side*Z≤hi i-lo i) :
    ∀ i, -(C+1)*(Z/K)≤rescaledEndpoint lo u K i ∧
      rescaledEndpoint hi u K i≤(C+1)*(Z/K) ∧
      side*(Z/K)≤rescaledEndpoint hi u K i-rescaledEndpoint lo u K i := by
  have hKr : 0<(K:ℝ):=by exact_mod_cast hK
  intro i
  have hu₀ : (0:ℝ)≤u i:=by exact_mod_cast (hu i).1
  have hu₁ : (u i:ℝ)≤K:=by exact_mod_cast (hu i).2
  have hl : -(C+1)*Z≤lo i-u i:=by nlinarith [(hb i).1]
  have hh : hi i-u i≤(C+1)*Z:=by
    have hZ₀ : 0≤Z:=hKr.le.trans hZ
    nlinarith [(hb i).2]
  dsimp only [rescaledEndpoint]
  constructor
  · simpa only [mul_div_assoc] using (div_le_div_of_nonneg_right hl hKr.le)
  constructor
  · simpa only [mul_div_assoc] using (div_le_div_of_nonneg_right hh hKr.le)
  · have he : (hi i-(u i:ℝ))/(K:ℝ)-(lo i-u i)/K=(hi i-lo i)/K:=by ring
    rw [he,←mul_div_assoc]
    exact div_le_div_of_nonneg_right (hs i) hKr.le

end RoughSamplingWeights
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RealPolynomialDegree
universe u v
variable {σ : Type u} {τ : Type v}

lemma affine_substitution_totalDegree (p : MvPolynomial σ ℝ)
    (F : σ → MvPolynomial τ ℝ) (hF : ∀ i,(F i).totalDegree≤1) :
    (MvPolynomial.eval₂ MvPolynomial.C F p).totalDegree≤p.totalDegree := by
  classical
  have he : MvPolynomial.eval₂ MvPolynomial.C F p=
      ∑ s∈p.support,MvPolynomial.C (p.coeff s)*s.prod (fun i e=>F i^e):=by
    conv_lhs => rw [p.as_sum]
    simp only [MvPolynomial.eval₂_sum,MvPolynomial.eval₂_monomial]
  rw [he]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  calc
    _≤(MvPolynomial.C (p.coeff s) : MvPolynomial τ ℝ).totalDegree+
      (s.prod (fun i e=>F i^e)).totalDegree:=MvPolynomial.totalDegree_mul _ _
    _=(s.prod (fun i e=>F i^e)).totalDegree:=by simp
    _≤∑ i∈s.support,(F i^s i).totalDegree:=MvPolynomial.totalDegree_finsetProd _ _
    _≤∑ i∈s.support,s i:=by
      apply Finset.sum_le_sum
      intro i _
      exact (MvPolynomial.totalDegree_pow (F i) (s i)).trans (by simpa using Nat.mul_le_mul_left (s i) (hF i))
    _≤p.totalDegree:=MvPolynomial.le_totalDegree hs

 

theorem affine_comp {f : (σ → ℝ) → ℝ} {d : ℕ} (hf : HasDegree f d)
    (a b : σ → ℝ) (θ : σ → τ) :
    HasDegree (fun x : τ → ℝ=>f (fun i=>a i+b i*x (θ i))) d := by
  obtain ⟨p,hp,he⟩:=hf
  let F : σ → MvPolynomial τ ℝ:=fun i=>MvPolynomial.C (a i)+MvPolynomial.C (b i)*MvPolynomial.X (θ i)
  have hF : ∀ i,(F i).totalDegree≤1:=by
    intro i
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · simp [MvPolynomial.totalDegree_C]
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  refine ⟨MvPolynomial.eval₂ MvPolynomial.C F p,(affine_substitution_totalDegree p F hF).trans hp,?_⟩
  intro x
  dsimp only
  rw [he]
  clear hp he
  induction p using MvPolynomial.induction_on with
  | C c=>simp
  | add p q hp hq=>simpa only [MvPolynomial.eval₂_add,MvPolynomial.eval_add] using congrArg₂ (·+·) hp hq
  | mul_X p i hp=>simp [F,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_X,MvPolynomial.eval_mul,hp]

end RealPolynomialDegree

end
end
end
end

end OAI
