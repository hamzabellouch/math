import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RegularResidue01
import OAI.Combinatorics.SumProduct.Alignment.UniformSlow01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
noncomputable section
open scoped BigOperators
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RegularResiduePieces
open RoughSamplingWeights RegularBoxPartition FinitePieceAverages
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 

omit [DecidableEq ι] in
theorem uniform_error_threshold [DecidableEq ι] (c B V ε : ℝ) (hc : 0<c) (hB : 0≤B)
    (hV : 0≤V) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ (Z q t : ℝ),0<Z → 0<q → 0<t → q+t≤δ*Z →
      ∀ (lo hi : ι → ℝ),(∀ i,c*Z≤hi i-lo i) →
      (∀ i,4*q≤hi i-lo i) ∧ (∀ i,4*t≤hi i-lo i) ∧
      B*(V*((∑ i,8*q/(hi i-lo i))+(∑ i,8*t/(hi i-lo i))))≤ε := by
  let d : ℝ:=Fintype.card ι
  let T : ℝ:=B*V*(d*8/c)
  have hd : 0≤d:=by dsimp [d]; positivity
  have hT : 0≤T:=by dsimp [T]; positivity
  let δ : ℝ:=min (c/4) (ε/(T+1))
  have hδ : 0<δ:=lt_min (by positivity) (div_pos hε (by linarith))
  have hδc : δ≤c/4:=min_le_left _ _
  have hδT : δ≤ε/(T+1):=min_le_right _ _
  refine ⟨δ,hδ,?_⟩
  intro Z q t hZ hq ht hqt lo hi hside
  have hqδ : q≤δ*Z:=by linarith
  have htδ : t≤δ*Z:=by linarith
  have hs : 4*δ*Z≤c*Z:=by
    have h₀ : 4*δ≤c:=by linarith
    exact mul_le_mul_of_nonneg_right h₀ hZ.le
  have hsq (i : ι) : 4*q≤hi i-lo i:=by
    have :=hside i
    nlinarith
  have hst (i : ι) : 4*t≤hi i-lo i:=by
    have :=hside i
    nlinarith
  refine ⟨hsq,hst,?_⟩
  have herr : (∑ i,8*q/(hi i-lo i))+(∑ i,8*t/(hi i-lo i))≤d*(8*δ/c):=by
    rw [←Finset.sum_add_distrib]
    calc
      _≤∑ _i:ι,8*δ/c:=by
        apply Finset.sum_le_sum
        intro i _
        have hL : 0<hi i-lo i:=lt_of_lt_of_le (mul_pos hc hZ) (hside i)
        have he : 8*q/(hi i-lo i)+8*t/(hi i-lo i)=8*(q+t)/(hi i-lo i):=by ring
        rw [he]
        calc
          _≤8*(δ*Z)/(hi i-lo i):=div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hqt (by norm_num)) hL.le
          _≤8*(δ*Z)/(c*Z):=div_le_div_of_nonneg_left (by positivity) (mul_pos hc hZ) (hside i)
          _=8*δ/c:=by field_simp
      _=d*(8*δ/c):=by simp [d]
  have hE : B*(V*((∑ i,8*q/(hi i-lo i))+(∑ i,8*t/(hi i-lo i))))≤T*δ:=by
    calc
      _≤B*(V*(d*(8*δ/c))):=mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left herr hV) hB
      _=T*δ:=by dsimp [T]; ring
  have htδ : (T+1)*δ≤ε:=by
    have hh:=(le_div_iff₀ (by linarith : 0<T+1)).mp hδT
    nlinarith
  exact hE.trans (by nlinarith)

 

theorem uniform_piece_selection (M K : ℕ) (hM : 0<M) (hK : 0<K) [NeZero K]
    (c B ε : ℝ) (hc : 0<c) (hB : 0≤B) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ (Z : ℝ),0<Z → ∀ (lo hi : ι → ℝ),
      (∀ i,c*Z≤hi i-lo i) → ∀ (a b : ι → ℤ) (q t : ℕ),
      0<q → 0<t → q.Coprime K → t.Coprime K → (q:ℝ)+t≤δ*Z →
      ∀ (f g : (ι → ℤ) → ℂ),
      (∀ x∈boxIndices lo hi (fun i=>(b i:ℝ)) t,‖g x‖≤B) → ∀ η : ℝ,
      η≤‖mean (boxIndices lo hi (fun i=>(a i:ℝ)) q) f-
        mean (boxIndices lo hi (fun i=>(b i:ℝ)) t) g‖ →
      ∃ (hL : ∀ i,lo i<hi i) (z : (ι → Fin M)×(ι → ZMod K)),
        (fiber (boxIndices lo hi (fun i=>(a i:ℝ)) q) (label lo hi hL M hM a q K) z).Nonempty ∧
        η-ε≤‖mean (fiber (boxIndices lo hi (fun i=>(a i:ℝ)) q) (label lo hi hL M hM a q K) z) f-
          mean (fiber (boxIndices lo hi (fun i=>(b i:ℝ)) t) (label lo hi hL M hM b t K) z) g‖ := by
  obtain ⟨δ,hδ,h⟩:=uniform_error_threshold (ι:=ι) c B
    (Fintype.card ((ι → Fin M)×(ι → ZMod K))) ε hc hB (by positivity) hε
  refine ⟨δ,hδ,?_⟩
  intro Z hZ lo hi hside a b q t hq ht hqK htK hqt f g hg η hd
  have hqr : 0<(q:ℝ):=by exact_mod_cast hq
  have htr : 0<(t:ℝ):=by exact_mod_cast ht
  have hL : ∀ i,lo i<hi i:=fun i=>sub_pos.mp (lt_of_lt_of_le (mul_pos hc hZ) (hside i))
  obtain ⟨hsq,hst,he⟩:=h Z q t hZ hqr htr hqt lo hi hside
  obtain ⟨z,hz,he⟩:=select_common_piece lo hi hL M hM a b q t K hq ht hK hqK htK
    hsq hst f g B hB hg η ε hd he
  exact ⟨hL,z,hz,he⟩

end RegularResiduePieces
end
 
end

section
 

 

noncomputable section
open scoped BigOperators NNReal
namespace RoughKernelFactorization
open RationalLattice MalcevCharacters UniformSlowPolynomials
open RoughSamplingWeights RegularBoxPartition RegularResiduePieces FinitePieceAverages
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G (n+1)) (hsk : SecondKind c)
variable (χ : G →* Multiplicative ℝ) (Γ : Subgroup G)
variable (R : Reduction c hsk χ Γ)
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
variable {X : Type*} [PseudoMetricSpace X] (v : (G⧸Γ) ≃ₜ X)
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

def sampledTest (e : κ → ι → ℕ) (coeff : κ → ℝ) (offset : ι → ℤ) (q : ℕ)
    (F : X → ℂ) (tailPoint : (ι → ℤ) → G⧸Γ) (x : ι → ℤ) : ℂ:=
  F (v ((R.flow c hsk χ Γ (Multiplicative.ofAdd
    (form e coeff (fun i=>(offset i:ℝ)+q*x i)))) • tailPoint x))

def frozenSampledTest (e : κ → ι → ℕ) (coeff : κ → ℝ)
    (lo hi : ι → ℝ) (hL : ∀ i,lo i<hi i) (M : ℕ) (hM : 0<M)
    (offset : ι → ℤ) (q : ℕ) (F : X → ℂ) (tailPoint : (ι → ℤ) → G⧸Γ)
    (x : ι → ℤ) : ℂ:=
  F (v ((R.flow c hsk χ Γ (Multiplicative.ofAdd (form e coeff
    (fun i=>left (lo i) (hi i) M
      (cell lo hi hL M hM (fun j=>(offset j:ℝ)+q*x j) i))))) • tailPoint x))

include hΓ in
 

theorem regular_sample_freezing (e : κ → ι → ℕ) (A C : ℝ) (hA : 0≤A) (hC : 0≤C)
    (L : ℝ≥0) (ε : ℝ) (hε : 0<ε) :
    ∃ M : ℕ,∃ hM : 0<M, ∀ Z : ℝ,0<Z → ∀ coeff : κ → ℝ,
      (∀ k,|coeff k| * Z^(∑ i,e k i)≤A) →
      ∀ (lo hi : ι → ℝ) (hL : ∀ i,lo i<hi i),
      (∀ i,-(C*Z)≤lo i ∧ hi i≤C*Z) → ∀ (offset : ι → ℤ) (q : ℕ),0<q →
      ∀ (F : X → ℂ),LipschitzWith L F → ∀ (tailPoint : (ι → ℤ) → G⧸Γ),
      ‖mean (boxIndices lo hi (fun i=>(offset i:ℝ)) q)
          (sampledTest c hsk χ Γ R v e coeff offset q F tailPoint)-
        mean (boxIndices lo hi (fun i=>(offset i:ℝ)) q)
          (frozenSampledTest c hsk χ Γ R v e coeff lo hi hL M hM offset q F tailPoint)‖≤ε := by
  obtain ⟨T,lam,hT,hlam,hfreeze⟩:=polynomial_slow_freezing c hsk χ Γ R hΓ v e A C hA hC L ε hε
  obtain ⟨M,hM,hfine⟩:=fine_partition (2*C) lam hlam
  refine ⟨M,hM,?_⟩
  intro Z hZ coeff hcoeff lo hi hL hb offset q hq F hF tailPoint
  apply mean_error _ _ _ ε hε.le
  intro x hx
  have hqr : 0<(q:ℝ):=by exact_mod_cast hq
  have hphys:= (mem_boxIndices lo hi (fun i=>(offset i:ℝ)) q hqr x).mp hx
  let p : ι → ℝ:=fun i=>(offset i:ℝ)+q*x i
  let b : ι → Fin M:=cell lo hi hL M hM p
  let y : ι → ℝ:=fun i=>left (lo i) (hi i) M (b i)
  have hyphys : ∀ i,y i≤p i ∧ p i<right (lo i) (hi i) M (b i):=by
    exact (cell_eq_iff lo hi hL M hM p hphys b).mp rfl
  have hp : ∀ i,|p i|≤C*Z:=by
    intro i
    rw [abs_le]
    exact ⟨(hb i).1.trans (hphys i).1,(hphys i).2.le.trans (hb i).2⟩
  have hy : ∀ i,|y i|≤C*Z:=by
    intro i
    rw [abs_le]
    have he:=endpoints (lo i) (hi i) (hL i) M hM (b i)
    exact ⟨(hb i).1.trans he.1,((hyphys i).1.trans (hphys i).2.le).trans (hb i).2⟩
  have hpy : ∀ i,|p i-y i|<lam*Z:=by
    intro i
    have hwidth:=hfine Z hZ (lo i) (hi i) (hL i) (by nlinarith [(hb i).1,(hb i).2]) (b i)
    rw [abs_of_nonneg (sub_nonneg.mpr (hyphys i).1)]
    dsimp only [y]
    linarith [(hyphys i).2]
  exact ((hfreeze Z hZ coeff hcoeff p y hp hy).2 hpy F hF (tailPoint x)).le

end RoughKernelFactorization
end
 
end

section
 

 

noncomputable section
open scoped BigOperators NNReal
namespace RoughKernelFactorization
open RationalLattice MalcevCharacters UniformSlowPolynomials
open RoughSamplingWeights RegularBoxPartition RegularResiduePieces FinitePieceAverages
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G (n+1)) (hsk : SecondKind c)
variable (χ : G →* Multiplicative ℝ) (Γ : Subgroup G)
variable (R : Reduction c hsk χ Γ)
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
variable {X : Type*} [PseudoMetricSpace X] (v : (G⧸Γ) ≃ₜ X)
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

include hΓ in
 

theorem regular_sample_select_frozen (e : κ → ι → ℕ) (A C side B : ℝ)
    (hA : 0≤A) (hC : 0≤C) (hside : 0<side) (hB : 0≤B)
    (L : ℝ≥0) (K : ℕ) (hK : 0<K) [NeZero K] (ε : ℝ) (hε : 0<ε) :
    ∃ M : ℕ,∃ hM : 0<M,∃ δ : ℝ,0<δ ∧
    ∀ Z : ℝ,0<Z → ∀ coeff₁ coeff₂ : κ → ℝ,
    (∀ k,|coeff₁ k| * Z^(∑ i,e k i)≤A) →
    (∀ k,|coeff₂ k| * Z^(∑ i,e k i)≤A) →
    ∀ (lo hi : ι → ℝ) (hL : ∀ i,lo i<hi i),
    (∀ i,-(C*Z)≤lo i ∧ hi i≤C*Z) →
    (∀ i,side*Z≤hi i-lo i) → ∀ (a b : ι → ℤ) (q t : ℕ),
    0<q → 0<t → q.Coprime K → t.Coprime K → (q:ℝ)+t≤δ*Z →
    ∀ (F₁ F₂ : X → ℂ),LipschitzWith L F₁ → LipschitzWith L F₂ →
    (∀ x,‖F₂ x‖≤B) → ∀ (tail₁ tail₂ : (ι → ℤ) → G⧸Γ),∀ η : ℝ,
    η≤‖mean (boxIndices lo hi (fun i=>(a i:ℝ)) q)
        (sampledTest c hsk χ Γ R v e coeff₁ a q F₁ tail₁)-
      mean (boxIndices lo hi (fun i=>(b i:ℝ)) t)
        (sampledTest c hsk χ Γ R v e coeff₂ b t F₂ tail₂)‖ →
    ∃ z : (ι → Fin M)×(ι → ZMod K),
      (fiber (boxIndices lo hi (fun i=>(a i:ℝ)) q) (label lo hi hL M hM a q K) z).Nonempty ∧
      η-3*ε≤‖mean (fiber (boxIndices lo hi (fun i=>(a i:ℝ)) q) (label lo hi hL M hM a q K) z)
          (frozenSampledTest c hsk χ Γ R v e coeff₁ lo hi hL M hM a q F₁ tail₁)-
        mean (fiber (boxIndices lo hi (fun i=>(b i:ℝ)) t) (label lo hi hL M hM b t K) z)
          (frozenSampledTest c hsk χ Γ R v e coeff₂ lo hi hL M hM b t F₂ tail₂)‖ := by
  obtain ⟨M,hM,hfreeze⟩:=regular_sample_freezing c hsk χ Γ R hΓ v e A C hA hC L ε hε
  obtain ⟨δ,hδ,hselect⟩:=uniform_piece_selection (ι:=ι) M K hM hK side B ε hside hB hε
  refine ⟨M,hM,δ,hδ,?_⟩
  intro Z hZ coeff₁ coeff₂ hc₁ hc₂ lo hi hL hb hsz a b q t hq ht hqK htK hqt
    F₁ F₂ hF₁ hF₂ hbound tail₁ tail₂ η hd
  let S:=boxIndices lo hi (fun i=>(a i:ℝ)) q
  let T:=boxIndices lo hi (fun i=>(b i:ℝ)) t
  let f:=frozenSampledTest c hsk χ Γ R v e coeff₁ lo hi hL M hM a q F₁ tail₁
  let g:=frozenSampledTest c hsk χ Γ R v e coeff₂ lo hi hL M hM b t F₂ tail₂
  let u:=mean S (sampledTest c hsk χ Γ R v e coeff₁ a q F₁ tail₁)
  let w:=mean T (sampledTest c hsk χ Γ R v e coeff₂ b t F₂ tail₂)
  have hu : ‖u-mean S f‖≤ε:=hfreeze Z hZ coeff₁ hc₁ lo hi hL hb a q hq F₁ hF₁ tail₁
  have hw : ‖w-mean T g‖≤ε:=hfreeze Z hZ coeff₂ hc₂ lo hi hL hb b t ht F₂ hF₂ tail₂
  have hdiff : η-2*ε≤‖mean S f-mean T g‖:=by
    have h₁:=norm_sub_le (u-mean S f) (w-mean S f)
    have h₂:=norm_sub_le (w-mean T g) (mean S f-mean T g)
    have he₁ : (u-mean S f)-(w-mean S f)=u-w:=by ring
    have he₂ : (w-mean T g)-(mean S f-mean T g)=w-mean S f:=by ring
    rw [he₁] at h₁
    rw [he₂] at h₂
    change η≤‖u-w‖ at hd
    linarith
  have hg : ∀ x∈T,‖g x‖≤B:=by
    intro x _
    exact hbound _
  obtain ⟨hL',z,hz,hd'⟩:=hselect Z hZ lo hi hsz a b q t hq ht hqK htK hqt f g hg (η-2*ε) hdiff
  refine ⟨z,hz,?_⟩
  change η-3*ε≤‖mean (fiber S (label lo hi hL M hM a q K) z) f-
    mean (fiber T (label lo hi hL M hM b t K) z) g‖
  linarith [hd']

end RoughKernelFactorization

end
end
end
end

end OAI
