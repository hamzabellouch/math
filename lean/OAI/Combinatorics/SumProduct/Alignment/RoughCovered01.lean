import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughFace03
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
noncomputable section
end
end

section

section
noncomputable section
namespace RoughCoveredFace
open RoughFaceShift
open RationalLattice MalcevCharacters RealPolynomialDegree RoughScales Filter
open RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open scoped BigOperators Topology
variable {G : Type} [Group G] [TopologicalSpace G] {dim : ℕ}
variable (Γ : Subgroup G) [MetricSpace (G⧸Γ)]
variable [IsTopologicalGroup G] (c : RealCoordinates G dim)

 

theorem source_face_decay (Λ : Subgroup G) (hle : Λ≤Γ) (hsk : SecondKind c)
    (hΛ : ∀ g : G,g∈Λ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (htop : (inferInstance : MetricSpace (G⧸Γ)).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace Γ)
    (m v D d : ℕ) (hd : 0<d) (c₀ C₀ : ℝ) (B K : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η)
    (w M : ℕ→ℕ) (S : ℕ → Fin m → ℝ) (Z H : ℕ→ℝ)
    (r : ℕ → Fin m → ℤ) (L : ℕ→ℤ)
    (hw : Tendsto w atTop atTop) (hS : ∀ j,Tendsto (fun n=>S n j) atTop atTop)
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun n=>Z n/(1+∑ j,S n j)^a) atTop atTop)
    (hH : ∀ n,0≤H n) (hHZ : Tendsto (fun n=>H n/Z n) atTop (𝓝 0))
    (hM : ∀ n,0<M n) (hMs : ∀ n,Smooth (w n) (M n:ℤ))
    (hL : ∀ n,0<L n) (hsm : ∀ n,Smooth (w n) (L n))
    (hWL : ∀ n,(primorial (w n):ℤ)∣L n)
    (hr : ∀ n j,(r n j).natAbs.Coprime (primorial (w n)))
    (hSL : ∀ j,Tendsto (fun n=>S n j/(L n:ℝ)) atTop atTop) :
    ∀ ε : ℝ,0<ε →∀ᶠ n in atTop,
      ∀ (A : Fin v → ℤ) (P : (Fin (m+v)→ℝ)→G),
      (∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D) →
      ∀ (σ : (G⧸Γ) → (G⧸Γ)),LipschitzWith K σ →
      ∀ h : (Fin m → ℤ) → Fin v → ℤ,
      (∀ t∈productTimes (S n) (r n) (L n),∀ i,(d:ℤ)∣h t i ∧ |(h t i:ℝ)|≤H n) →
      (∀ t∈productTimes (S n) (r n) (L n),∀ x : Fin v → ℤ,
        σ (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))=
          QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>((x i+h t i:ℤ):ℝ))))) →
      ((exceptionalFace Γ m v c₀ C₀ B η (Z n) d (M n) A P σ (S n) (r n) (L n)).card:ℝ)/
        ((productTimes (S n) (r n) (L n)).card:ℝ)<ε := by
  classical
  let B' : NNReal := B*(K+1)
  have hB' : 0<B' := mul_pos hB (by positivity)
  have hBB : B≤B' := by
    dsimp [B']
    calc
      B=B*1 := by ring
      _≤B*(K+1) := mul_le_mul_of_nonneg_left (by nlinarith [K.2]) B.2
  have hBK : B*K≤B' := by
    dsimp [B']
    rw [mul_add,mul_one]
    exact le_add_of_nonneg_right B.2
  have hz : Tendsto Z atTop atTop := by
    have h := domination_smaller (S:=fun _=>1) (T:=fun n=>totalScale (S n))
      (by filter_upwards [] with n; norm_num) (totalScale_pos_eventually S hS) hZ
    simpa using h 1 zero_lt_one
  have herr : Tendsto (fun n=>(8*(B:ℝ)*(v:ℝ)/c₀)*(H n/Z n)) atTop (𝓝 0) := by
    simpa using hHZ.const_mul (8*(B:ℝ)*(v:ℝ)/c₀)
  intro ε hε
  have hp := source_product_cover_decay c Γ Λ hle hsk hΛ htop m v D d hd c₀ C₀ B' (η/4)
    hc₀ hC₀ hB' (by positivity) w M S Z r L hw hS hZ hM hMs hL hsm hWL hr hSL ε hε
  filter_upwards [hp,hz.eventually (eventually_ge_atTop (4*(d:ℝ)/c₀)),
    herr.eventually (gt_mem_nhds (by positivity : (0:ℝ)<η/4))] with n hpn hzn hen
  intro A P hP σ hσ h hh hid
  have hW : 4*(d:ℝ)≤c₀*Z n := by
    have ht := (div_le_iff₀ hc₀).mp hzn
    nlinarith
  have hsub : exceptionalFace Γ m v c₀ C₀ B η (Z n) d (M n) A P σ (S n) (r n) (L n) ⊆
      exceptionalProduct Γ m v c₀ C₀ B' (η/4) (Z n) d (M n) A P (S n) (r n) (L n) := by
    intro t ht
    obtain ⟨ht,hbad⟩ := Finset.mem_filter.mp ht
    apply Finset.mem_filter.mpr
    refine ⟨ht,?_⟩
    by_contra hgood
    obtain ⟨lo,hi,res,test,hside,hbox,hLip,hnorm,hlarge⟩ := hbad
    have hcompare (F : (G⧸Γ) → ℂ) (hFL : LipschitzWith B' F) (hFn : ∀ y,‖F y‖≤B') :
        ‖mean (physicalResidueBox lo hi res d)
          (fun x=>F (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ))))))-
        mean (nestedBox lo hi res A d (M n) (∏ j,t j))
          (fun x=>F (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ))))))‖<η/4 := by
      apply lt_of_not_ge
      intro hh
      exact hgood ⟨lo,hi,res,F,hside,hbox,hFL,hFn,hh⟩
    have hplain := hcompare test (hLip.weaken hBB)
      (fun y=>(hnorm y).trans (by exact_mod_cast hBB))
    have hface := hcompare (fun y=>test (σ y)) ((hLip.comp hσ).weaken hBK)
      (fun y=>(hnorm (σ y)).trans (by exact_mod_cast hBB))
    let f : (Fin v → ℤ) → ℂ := fun x=>test
      (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))
    have hshift := residueMean_translation lo hi res (h t) d hd (B:ℝ) (c₀*Z n) (H n)
      hB hW hside (hH n) (hh t ht) f (fun x=>hnorm _)
    have he : (fun x : Fin v → ℤ=>test
        (σ (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))))=
        fun x=>f (x+h t) := by
      funext x
      rw [hid t ht x]
      rfl
    have hsmall : ‖mean (physicalResidueBox lo hi res d) (fun x=>f (x+h t))-
        mean (physicalResidueBox lo hi res d) f‖<η/4 := by
      apply hshift.trans_lt
      convert hen using 1
      ring
    rw [← he] at hsmall
    let X := mean (nestedBox lo hi res A d (M n) (∏ j,t j))
      (fun x=>test (σ (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))))
    let Y := mean (physicalResidueBox lo hi res d)
      (fun x=>test (σ (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))))
    let U := mean (physicalResidueBox lo hi res d) f
    let V := mean (nestedBox lo hi res A d (M n) (∏ j,t j)) f
    have htri : ‖X-V‖≤‖X-Y‖+‖Y-U‖+‖U-V‖ := by
      calc
        _≤‖X-U‖+‖U-V‖ := norm_sub_le_norm_sub_add_norm_sub X U V
        _≤_ := add_le_add (norm_sub_le_norm_sub_add_norm_sub X Y U) (le_refl ‖U-V‖)
    change η≤‖X-V‖ at hlarge
    change ‖U-V‖<η/4 at hplain
    change ‖Y-X‖<η/4 at hface
    rw [norm_sub_rev] at hface
    change ‖Y-U‖<η/4 at hsmall
    linarith
  exact (div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub)
    (Nat.cast_nonneg _)).trans_lt (hpn A P hP)

end RoughCoveredFace
end

end

section
noncomputable section
namespace RoughCoveredFace
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

end RoughCoveredFace

end

end

section
noncomputable section
namespace RoughCoveredFace
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
  have hh := source_conditional_face_decay (Γ:=Γ) (c:=c) Λ hle hsk hΛ htop m v D d hd
    c₀ C₀ B K η hc₀ hC₀ hB hη w M (fun n=>(b n).S) (fun n=>(b n).Z) H
    (fun n=>(b n).Q) (fun n=>(b n).Δ) (fun n=>(b n).a)
    (fun n=>(b n).r) L hw hS hZs hH hHsmall hM hMs hL hsm hWL
    (fun n=>(hb n).2.2.1) hSL hbin ε hε
  filter_upwards [hh] with n hn
  intro z hz
  by_contra he
  exact hfail n ⟨z,hz,he⟩ hn

end RoughCoveredFace

end
end
end

end OAI
