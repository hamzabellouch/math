import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughTopological01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
noncomputable section
end

end

section
noncomputable section
namespace RoughTopologicalFace
open RoughCoveredFace
open RoughFaceShift
open RationalLattice MalcevCharacters RealPolynomialDegree RoughScales Filter
open RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open scoped BigOperators Topology
variable {G : Type} [Group G] [TopologicalSpace G] {dim : ℕ}
variable (Γ : Subgroup G) [MetricSpace (G⧸Γ)]
variable [IsTopologicalGroup G] (c : RealCoordinates G dim)

 

theorem source_conditional_face_decay (Λ : Subgroup G) (hle : Λ≤Γ) (hsk : SecondKind c)
    (hΛ : ∀ g : G,g∈Λ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
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
      ∀ (σ : (G⧸Γ) → (G⧸Γ)),Approximable B K η σ →
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
  have hf := source_face_decay (Γ:=Γ) (c:=c) Λ hle hsk hΛ htop m v D d hd c₀ C₀ B K η
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

end RoughTopologicalFace

end

end

section
noncomputable section
namespace RoughTopologicalFace
open RoughCoveredFace
open RoughFaceShift
open RationalLattice MalcevCharacters RealPolynomialDegree RoughScales Filter
open RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open scoped BigOperators Topology
variable {G : Type} [Group G] [TopologicalSpace G] {dim : ℕ}
variable (Γ : Subgroup G) [MetricSpace (G⧸Γ)]
variable [IsTopologicalGroup G] (c : RealCoordinates G dim)

 

theorem conditional_face_uniform (Λ : Subgroup G) (hle : Λ≤Γ) (hsk : SecondKind c)
    (hΛ : ∀ g : G,g∈Λ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
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
      ∀ (σ : (G⧸Γ) → (G⧸Γ)),Approximable B K η σ →
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
      ∀ (σ : (G⧸Γ) → (G⧸Γ)),Approximable B K η σ →
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
  have hh := source_conditional_face_decay (Γ:=Γ) (c:=c) Λ hle hsk hΛ htop m v D d hd
    c₀ C₀ B K η hc₀ hC₀ hB hη w M (fun n=>(b n).S) (fun n=>(b n).Z) H
    (fun n=>(b n).Q) (fun n=>(b n).Δ) (fun n=>(b n).a)
    (fun n=>(b n).r) L hw hS hZs hH hHsmall hM hMs hL hsm hWL
    (fun n=>(hb n).2.2.1) hSL hbin ε hε
  filter_upwards [hh] with n hn
  intro z hz
  by_contra he
  exact hfail n ⟨z,hz,he⟩ hn

end RoughTopologicalFace
end

end

section
noncomputable section
namespace RoughTopologicalFace
open RoughCoveredFace
open RoughFaceShift
open RationalLattice MalcevCharacters RealPolynomialDegree RoughScales Filter
open RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open scoped BigOperators Topology
variable {G : Type} [Group G] [TopologicalSpace G] {dim : ℕ}
variable (Γ : Subgroup G) [MetricSpace (G⧸Γ)]
variable [IsTopologicalGroup G] (c : RealCoordinates G dim)

 
theorem raw_conditional_face_uniform (Λ : Subgroup G) (hle : Λ≤Γ) (hsk : SecondKind c)
    (hΛ : ∀ g : G,g∈Λ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
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
      ∀ X W : ℕ,(W:ℤ)∣(M n:ℤ) → b.a.natAbs.Coprime W →
      (∀ t∈productTimes b.S b.r (L n),(X:ℝ)≤b.Q/(∏ j,(t j:ℝ))) →
      (∀ t∈productTimes b.S b.r (L n),(b.Q+b.Δ)/(∏ j,(t j:ℝ))≤(X:ℝ)^2) →
      ∀ (A : Fin v → ℤ) (P : (Fin (m+v)→ℝ)→G),
      (∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D) →
      ∀ (σ : (G⧸Γ) → (G⧸Γ)),Approximable B K η σ →
      ∀ h : (Fin m → ℤ) → Fin v → ℤ,
      (∀ t∈productTimes b.S b.r (L n),∀ i,(d:ℤ)∣h t i ∧ |(h t i:ℝ)|≤H n) →
      (∀ t∈productTimes b.S b.r (L n),∀ x : Fin v → ℤ,
        σ (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))=
          QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>((x i+h t i:ℤ):ℝ))))) →
      HarmonicExposure.rawFiberMass
        (exceptionalFace Γ m v c₀ C₀ B η b.Z d (M n) A P σ b.S b.r (L n))
        X W b.Q b.Δ b.a (M n) /
      HarmonicExposure.rawFiberMass (productTimes b.S b.r (L n))
        X W b.Q b.Δ b.a (M n)<ε
 := by
  classical
  intro ε hε
  have hu := conditional_face_uniform (Γ:=Γ) (c:=c) Λ hle hsk hΛ htop m v D d hd
    c₀ C₀ B K η hc₀ hC₀ hB hη w M U V Z0 H L hw hU hUV hZ hH hHZ
    hM hMs hL hsm hWL hUL ε hε
  have hup : ∀ᶠ n in atTop,∀ j,0<U n j :=
    eventually_all.mpr (fun j=>(hU j).eventually (eventually_gt_atTop 0))
  filter_upwards [hu,hup] with n hn hUn
  intro b hb X W hWM ha hlo hhi A P hP σ hσ h hh hid
  have hτ : ∀ t∈productTimes b.S b.r (L n),0<∏ j,(t j:ℝ) := by
    intro t ht
    apply Finset.prod_pos
    intro j hj
    have htj := Fintype.mem_piFinset.mp ht j
    have htpos := (mem_times (b.S j) (b.r j) (L n) (t j) (hL n)).mp htj
    exact (hUn j).trans_le (((hb.1 j).1).trans htpos.1)
  have he (T : Finset (Fin m→ℤ)) (hT : T⊆productTimes b.S b.r (L n)) :=
    HarmonicExposure.rawFiberMass_eq_exposed T X W b.Q b.Δ b.a (M n)
      (by exact_mod_cast hM n) hWM ha
      (fun t ht=>hτ t (hT ht)) (fun t ht=>hlo t (hT ht)) (fun t ht=>hhi t (hT ht))
  have hsub : exceptionalFace Γ m v c₀ C₀ B η b.Z d (M n) A P σ b.S b.r (L n) ⊆
      productTimes b.S b.r (L n) := Finset.filter_subset _ _
  rw [he _ hsub,he _ (Finset.Subset.refl _)]
  exact hn b hb A P hP σ hσ h hh hid

end RoughTopologicalFace

end
end
end

end OAI
