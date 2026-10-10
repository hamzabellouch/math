import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.HarmonicExposure01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
noncomputable section
end
end
 

section
 
noncomputable section
namespace RoughFaceShift
open RationalLattice MalcevCharacters RealPolynomialDegree RoughScales Filter
open RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open scoped BigOperators Topology
variable {G : Type} [Group G] [TopologicalSpace G] {dim : ℕ}
variable (Γ : Subgroup G) [MetricSpace (G⧸Γ)]
variable [IsTopologicalGroup G] (c : RealCoordinates G dim)

 

theorem source_conditional_face_decay (hsk : SecondKind c)
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (htop : (inferInstance : MetricSpace (G⧸Γ)).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace Γ)
    (m v D d : ℕ) (hd : 0<d) (c₀ C₀ : ℝ) (B K : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η)
    (w M : ℕ→ℕ) (S : ℕ → Fin m → ℝ) (Z H Q Δ : ℕ→ℝ) (a : ℕ→ℤ)
    (r : ℕ → Fin m → ℤ) (L : ℕ→ℤ)
    (hw : Tendsto w atTop atTop) (hS : ∀ j,Tendsto (fun n=>S n j) atTop atTop)
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun n=>Z n/(1+∑ j,S n j)^a) atTop atTop)
    (hH : ∀ n,0≤H n) (hHZ : Tendsto (fun n=>H n/Z n) atTop (𝓝 0))
    (hM : ∀ n,0<M n) (hMs : ∀ n,Smooth (w n) (M n:ℤ))
    (hL : ∀ n,0<L n) (hsm : ∀ n,Smooth (w n) (L n))
    (hWL : ∀ n,(primorial (w n):ℤ)∣L n)
    (hr : ∀ n j,(r n j).natAbs.Coprime (primorial (w n)))
    (hSL : ∀ j,Tendsto (fun n=>S n j/(L n:ℝ)) atTop atTop)
    (hbin : ∀ᶠ n in atTop,0<Q n ∧ 0<Δ n ∧ Δ n≤Q n ∧
      4*(M n:ℝ)*(2^m*∏ j,S n j)≤Δ n) :
    ∀ ε : ℝ,0<ε →∀ᶠ n in atTop,
      ∀ (A : Fin v → ℤ) (P : (Fin (m+v)→ℝ)→G),
      (∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D) →
      ∀ (σ : (G⧸Γ) → (G⧸Γ)),LipschitzWith K σ →
      ∀ h : (Fin m → ℤ) → Fin v → ℤ,
      (∀ t∈productTimes (S n) (r n) (L n),∀ i,(d:ℤ)∣h t i ∧ |(h t i:ℝ)|≤H n) →
      (∀ t∈productTimes (S n) (r n) (L n),∀ x : Fin v → ℤ,
        σ (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))=
          QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>((x i+h t i:ℤ):ℝ))))) →
      (∑ t∈exceptionalFace Γ m v c₀ C₀ B η (Z n) d (M n) A P σ (S n) (r n) (L n),
        HarmonicExposure.exposedWeight (Q n) (Δ n) (a n) (M n) t)/
        (∑ t∈productTimes (S n) (r n) (L n),
          HarmonicExposure.exposedWeight (Q n) (Δ n) (a n) (M n) t)<ε := by
  classical
  have hK : (0:ℝ)<8*2^m := by positivity
  intro ε hε
  have hf := source_face_decay (Γ:=Γ) (c:=c) hsk hΓ htop m v D d hd c₀ C₀ B K η
    hc₀ hC₀ hB hη w M S Z H r L hw hS hZ hH hHZ hM hMs hL hsm hWL hr hSL
    (ε/(8*2^m)) (div_pos hε hK)
  have hpos : ∀ᶠ n in atTop,∀ j,0<S n j :=
    eventually_all.mpr (fun j=>(hS j).eventually (eventually_gt_atTop 0))
  have hne := productTimes_nonempty_eventually S r L hL hS hSL
  filter_upwards [hf,hpos,hne,hbin] with n hfn hsn htn hbn
  intro A P hP σ hσ h hh hid
  have hfrac := hfn A P hP σ hσ h hh hid
  have hdom := HarmonicExposure.conditional_fraction_le m (S n) (r n) (L n) (a n) (M n)
    (Q n) (Δ n) hsn (hL n) (by exact_mod_cast hM n) hbn.1 hbn.2.1 hbn.2.2.1 hbn.2.2.2
    htn (exceptionalFace Γ m v c₀ C₀ B η (Z n) d (M n) A P σ (S n) (r n) (L n))
    (Finset.filter_subset _ _)
  apply hdom.trans_lt
  have hh := mul_lt_mul_of_pos_left hfrac hK
  simpa only [mul_div_cancel₀ _ hK.ne'] using hh

end RoughFaceShift

end
end
 

section
noncomputable section
namespace RoughFaceShift
open RationalLattice MalcevCharacters RealPolynomialDegree RoughScales Filter
open RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open scoped BigOperators Topology
variable {G : Type} [Group G] [TopologicalSpace G] {dim : ℕ}
variable (Γ : Subgroup G) [MetricSpace (G⧸Γ)]
variable [IsTopologicalGroup G] (c : RealCoordinates G dim)

structure Exposure (m : ℕ) where
  S : Fin m → ℝ
  r : Fin m → ℤ
  Z : ℝ
  Q : ℝ
  Δ : ℝ
  a : ℤ

def Exposure.Legal {m : ℕ} (b : Exposure m) (U V : Fin m → ℝ)
    (Z0 : ℝ) (w M : ℕ) : Prop :=
  (∀ j,U j≤b.S j ∧ b.S j≤V j) ∧ Z0≤b.Z ∧
  (∀ j,(b.r j).natAbs.Coprime (primorial w)) ∧
  0<b.Q ∧ 0<b.Δ ∧ b.Δ≤b.Q ∧ 4*(M:ℝ)*(2^m*∏ j,b.S j)≤b.Δ

 

theorem conditional_face_uniform (hsk : SecondKind c)
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (htop : (inferInstance : MetricSpace (G⧸Γ)).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace Γ)
    (m v D d : ℕ) (hd : 0<d) (c₀ C₀ : ℝ) (B K : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η)
    (w M : ℕ→ℕ) (U V : ℕ → Fin m → ℝ) (Z0 H : ℕ→ℝ) (L : ℕ→ℤ)
    (hw : Tendsto w atTop atTop) (hU : ∀ j,Tendsto (fun n=>U n j) atTop atTop)
    (hUV : ∀ n j,U n j≤V n j)
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun n=>Z0 n/(1+∑ j,V n j)^a) atTop atTop)
    (hH : ∀ n,0≤H n) (hHZ : Tendsto (fun n=>H n/Z0 n) atTop (𝓝 0))
    (hM : ∀ n,0<M n) (hMs : ∀ n,Smooth (w n) (M n:ℤ))
    (hL : ∀ n,0<L n) (hsm : ∀ n,Smooth (w n) (L n))
    (hWL : ∀ n,(primorial (w n):ℤ)∣L n)
    (hUL : ∀ j,Tendsto (fun n=>U n j/(L n:ℝ)) atTop atTop) :
    ∀ ε : ℝ,0<ε →∀ᶠ n in atTop,
      ∀ b : Exposure m,b.Legal (U n) (V n) (Z0 n) (w n) (M n) →
      ∀ (A : Fin v → ℤ) (P : (Fin (m+v)→ℝ)→G),
      (∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D) →
      ∀ (σ : (G⧸Γ) → (G⧸Γ)),LipschitzWith K σ →
      ∀ h : (Fin m → ℤ) → Fin v → ℤ,
      (∀ t∈productTimes b.S b.r (L n),∀ i,(d:ℤ)∣h t i ∧ |(h t i:ℝ)|≤H n) →
      (∀ t∈productTimes b.S b.r (L n),∀ x : Fin v → ℤ,
        σ (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))=
          QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>((x i+h t i:ℤ):ℝ))))) →
      (∑ t∈exceptionalFace Γ m v c₀ C₀ B η b.Z d (M n) A P σ b.S b.r (L n),
        HarmonicExposure.exposedWeight b.Q b.Δ b.a (M n) t)/
        (∑ t∈productTimes b.S b.r (L n),
          HarmonicExposure.exposedWeight b.Q b.Δ b.a (M n) t)<ε
 := by
  classical
  intro ε hε
  let succeeds (n : ℕ) (b : Exposure m) : Prop :=
    ∀ (A : Fin v → ℤ) (P : (Fin (m+v)→ℝ)→G),
      (∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D) →
      ∀ (σ : (G⧸Γ) → (G⧸Γ)),LipschitzWith K σ →
      ∀ h : (Fin m → ℤ) → Fin v → ℤ,
      (∀ t∈productTimes b.S b.r (L n),∀ i,(d:ℤ)∣h t i ∧ |(h t i:ℝ)|≤H n) →
      (∀ t∈productTimes b.S b.r (L n),∀ x : Fin v → ℤ,
        σ (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))=
          QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>((x i+h t i:ℤ):ℝ))))) →
      (∑ t∈exceptionalFace Γ m v c₀ C₀ B η b.Z d (M n) A P σ b.S b.r (L n),
        HarmonicExposure.exposedWeight b.Q b.Δ b.a (M n) t)/
        (∑ t∈productTimes b.S b.r (L n),
          HarmonicExposure.exposedWeight b.Q b.Δ b.a (M n) t)<ε

  change ∀ᶠ n in atTop,∀ b : Exposure m,
    b.Legal (U n) (V n) (Z0 n) (w n) (M n) → succeeds n b
  have hchoice (n : ℕ) : ∃ b : Exposure m,
      b.Legal (U n) (V n) (Z0 n) (w n) (M n) ∧
      ((∃ b : Exposure m,b.Legal (U n) (V n) (Z0 n) (w n) (M n) ∧ ¬succeeds n b)
        → ¬succeeds n b) := by
    by_cases he : ∃ b : Exposure m,
      b.Legal (U n) (V n) (Z0 n) (w n) (M n) ∧ ¬succeeds n b
    · obtain ⟨b,hb,hf⟩ := he
      exact ⟨b,hb,fun _=>hf⟩
    · let Δ : ℝ := max 1 (4*(M n:ℝ)*(2^m*∏ j,U n j))
      refine ⟨⟨U n,fun _=>1,Z0 n,Δ,Δ,0⟩,?_,fun hh=>(he hh).elim⟩
      refine ⟨fun j=>⟨le_refl _,hUV n j⟩,le_refl _,?_,?_,?_,le_refl _,?_⟩
      · intro j
        simp
      · exact zero_lt_one.trans_le (le_max_left _ _)
      · exact zero_lt_one.trans_le (le_max_left _ _)
      · exact le_max_right _ _
  choose b hb hfail using hchoice
  have hS : ∀ j,Tendsto (fun n=>(b n).S j) atTop atTop := fun j=>
    tendsto_atTop_mono (fun n=>(hb n).1 j |>.1) (hU j)
  have hV : ∀ j,Tendsto (fun n=>V n j) atTop atTop := fun j=>
    tendsto_atTop_mono (fun n=>hUV n j) (hU j)
  have hspos := totalScale_pos_eventually (fun n=>(b n).S) hS
  have hvpos := totalScale_pos_eventually V hV
  have hzsmall := domination_smaller (S:=fun _=>1)
    (by filter_upwards [] with n; norm_num) hvpos hZ
  have hz0 : Tendsto Z0 atTop atTop := by
    simpa using hzsmall 1 zero_lt_one
  have hZs : ∀ a : ℝ,0<a →
      Tendsto (fun n=>(b n).Z/(1+∑ j,(b n).S j)^a) atTop atTop := by
    have hh := domination_smaller (S:=fun n=>totalScale (b n).S)
      (by filter_upwards [hspos] with n hn; linarith)
      (by filter_upwards [] with n
          dsimp [totalScale]
          have hh := Finset.sum_le_sum (s:=Finset.univ) (fun j _=>(hb n).1 j |>.2)
          linarith) hZ
    intro a ha
    apply tendsto_atTop_mono' atTop ?_ (hh a ha)
    filter_upwards [hspos] with n hn
    exact div_le_div_of_nonneg_right (hb n).2.1 (Real.rpow_nonneg (by linarith) _)
  have hHsmall : Tendsto (fun n=>H n/(b n).Z) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ hHZ
    · filter_upwards [hz0.eventually (eventually_gt_atTop 0)] with n hn
      exact div_nonneg (hH n) (hn.le.trans (hb n).2.1)
    · filter_upwards [hz0.eventually (eventually_gt_atTop 0)] with n hn
      exact div_le_div_of_nonneg_left (hH n) hn (hb n).2.1
  have hSL : ∀ j,Tendsto (fun n=>(b n).S j/(L n:ℝ)) atTop atTop := by
    intro j
    apply tendsto_atTop_mono (fun n=>?_) (hUL j)
    exact div_le_div_of_nonneg_right ((hb n).1 j).1 (by exact_mod_cast (hL n).le)
  have hbin : ∀ᶠ n in atTop,0<(b n).Q ∧ 0<(b n).Δ ∧ (b n).Δ≤(b n).Q ∧
      4*(M n:ℝ)*(2^m*∏ j,(b n).S j)≤(b n).Δ := by
    filter_upwards [] with n
    exact (hb n).2.2.2
  have hh := source_conditional_face_decay (Γ:=Γ) (c:=c) hsk hΓ htop m v D d hd
    c₀ C₀ B K η hc₀ hC₀ hB hη w M (fun n=>(b n).S) (fun n=>(b n).Z) H
    (fun n=>(b n).Q) (fun n=>(b n).Δ) (fun n=>(b n).a)
    (fun n=>(b n).r) L hw hS hZs hH hHsmall hM hMs hL hsm hWL
    (fun n=>(hb n).2.2.1) hSL hbin ε hε
  filter_upwards [hh] with n hn
  intro z hz
  by_contra he
  exact hfail n ⟨z,hz,he⟩ hn

end RoughFaceShift
end
end

section
noncomputable section
namespace HarmonicExposure
open RoughSamplingWeights RoughSourceExceptional RoughProductRemoval Finset
open scoped BigOperators

def pivotFiber (X : ℕ) (Q Δ τ : ℝ) (a M : ℤ) : Finset ℕ :=
  (Ico X (X^2)).filter (fun p=> M∣(p:ℤ)-a ∧ Q≤τ*p ∧ τ*p<Q+Δ)

lemma pivot_parameter_nonneg (X : ℕ) (Q Δ τ : ℝ) (a M : ℤ) (hM : 0<M) (_ : 0<τ)
    (hlo : (X:ℝ)≤Q/τ) {k : ℤ} (hk : k∈indices (Q/τ) ((Q+Δ)/τ) a M) :
    0≤a+M*k := by
  have hh := (mem_indices (Q/τ) ((Q+Δ)/τ) a M (by exact_mod_cast hM) k).mp hk
  have hx : (0:ℝ)≤(X:ℝ) := by positivity
  have hp : (0:ℝ)≤a+(M:ℝ)*(k:ℝ) := hx.trans (hlo.trans hh.1)
  exact_mod_cast hp

theorem pivotMass_eq_raw (X : ℕ) (Q Δ τ : ℝ) (a M : ℤ) (hM : 0<M) (hτ : 0<τ)
    (hlo : (X:ℝ)≤Q/τ) (hhi : (Q+Δ)/τ≤(X:ℝ)^2) :
    pivotMass Q Δ τ a M = ∑ p∈pivotFiber X Q Δ τ a M,(p:ℝ)⁻¹ := by
  classical
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hn (k : ℤ) (hk : k∈indices (Q/τ) ((Q+Δ)/τ) a M) :
      ((a+M*k).toNat:ℤ)=a+M*k :=
    Int.toNat_of_nonneg (pivot_parameter_nonneg X Q Δ τ a M hM hτ hlo hk)
  have hnr (k : ℤ) (hk : k∈indices (Q/τ) ((Q+Δ)/τ) a M) :
      ((a+M*k).toNat:ℝ)=(a:ℝ)+(M:ℝ)*(k:ℝ) := by exact_mod_cast hn k hk
  unfold pivotMass
  apply sum_bij (fun k _=>(a+M*k).toNat)
  · intro k hk
    have hh := (mem_indices (Q/τ) ((Q+Δ)/τ) a M hMr k).mp hk
    apply mem_filter.mpr
    constructor
    · apply mem_Ico.mpr
      constructor
      · have hh' := hlo.trans hh.1
        rw [←hnr k hk] at hh'
        exact_mod_cast hh'
      · have hh' := hh.2.trans_le hhi
        rw [←hnr k hk] at hh'
        exact_mod_cast hh'
    · refine ⟨?_,?_,?_⟩
      · rw [hn k hk]
        exact ⟨k,by ring⟩
      · rw [hnr k hk]
        simpa only [mul_comm] using (div_le_iff₀ hτ).mp hh.1
      · rw [hnr k hk]
        simpa only [mul_comm] using (lt_div_iff₀ hτ).mp hh.2
  · intro k hk l hl he
    have hh := congrArg (fun n : ℕ=>(n:ℤ)) he
    rw [hn k hk,hn l hl] at hh
    nlinarith
  · intro p hp
    obtain ⟨hpx,hcond⟩ := mem_filter.mp hp
    obtain ⟨k,hk⟩ := hcond.1
    have hpz : (p:ℤ)=a+M*k := by linarith
    have hpr : (p:ℝ)=(a:ℝ)+(M:ℝ)*(k:ℝ) := by exact_mod_cast hpz
    have hidx : k∈indices (Q/τ) ((Q+Δ)/τ) a M := by
      rw [mem_indices _ _ _ _ hMr]
      rw [←hpr]
      constructor
      · apply (div_le_iff₀ hτ).mpr
        nlinarith [hcond.2.1]
      · apply (lt_div_iff₀ hτ).mpr
        nlinarith [hcond.2.2]
    refine ⟨k,hidx,?_⟩
    rw [←hpz]
    simp
  · intro k hk
    rw [hnr k hk]

lemma residue_unit (W p : ℕ) (a M : ℤ) (hWM : (W:ℤ)∣M)
    (ha : a.natAbs.Coprime W) (hp : M∣(p:ℤ)-a) : W.Coprime p := by
  obtain ⟨b,hb⟩ := hWM
  obtain ⟨k,hk⟩ := hp
  have hc : IsCoprime a (W:ℤ) := Int.isCoprime_iff_nat_coprime.mpr (by simpa using ha)
  have hd := hc.add_mul_left_left (b*k)
  have he : a+(W:ℤ)*(b*k)=(p:ℤ) := by rw [hb] at hk; nlinarith
  rw [he] at hd
  have hh := Int.isCoprime_iff_nat_coprime.mp hd
  simpa only [Int.natAbs_natCast] using hh.symm

def rawFiberMass {m : ℕ} (T : Finset (Fin m→ℤ)) (X W : ℕ)
    (Q Δ : ℝ) (a M : ℤ) : ℝ :=
  ∑ t∈T, (∏ j,(t j:ℝ)⁻¹) *
    ∑ p∈pivotFiber X Q Δ (∏ j,(t j:ℝ)) a M, if W.Coprime p then (p:ℝ)⁻¹ else 0

theorem rawFiberMass_eq_exposed {m : ℕ} (T : Finset (Fin m→ℤ)) (X W : ℕ)
    (Q Δ : ℝ) (a M : ℤ) (hM : 0<M) (hWM : (W:ℤ)∣M) (ha : a.natAbs.Coprime W)
    (hτ : ∀ t∈T,0<∏ j,(t j:ℝ))
    (hlo : ∀ t∈T,(X:ℝ)≤Q/(∏ j,(t j:ℝ)))
    (hhi : ∀ t∈T,(Q+Δ)/(∏ j,(t j:ℝ))≤(X:ℝ)^2) :
    rawFiberMass T X W Q Δ a M=∑ t∈T,exposedWeight Q Δ a M t := by
  classical
  unfold rawFiberMass exposedWeight
  apply sum_congr rfl
  intro t ht
  congr 1
  rw [pivotMass_eq_raw X Q Δ _ a M hM (hτ t ht) (hlo t ht) (hhi t ht)]
  apply sum_congr rfl
  intro p hp
  rw [ite_eq_left (residue_unit W p a M hWM ha (mem_filter.mp hp).2.1)]

end HarmonicExposure

end
end

end OAI
