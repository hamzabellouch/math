import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughFace02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
noncomputable section
end
end

section
noncomputable section
namespace RoughFaceShift
open ProductExposureLabels ProductExposureLaw HarmonicExposure MeasureTheory
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

lemma jointFiber_filter {m : ℕ} (E : Set (Fin m→ℤ)) (X : Fin m→ℕ) (Xp W : ℕ)
    (S : Fin m→ℝ) (r : Fin m→ℤ) (L : ℤ) (Q Δ : ℝ) (a M : ℤ) :
    jointFiber E X Xp W S r L Q Δ a M =
      (jointFiber Set.univ X Xp W S r L Q Δ a M).filter (fun z=>(fun j=>(z.1 j:ℤ))∈E) := by
  ext z
  simp only [jointFiber,Finset.mem_filter,Set.mem_univ,true_and]
  tauto

lemma label_conditional_exact {m : ℕ} (X : Fin m→ℕ) (Xp W M : ℕ) (L : ℤ) (R : ℝ)
    (hW : 0<W) (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp)
    (hL : 0<L) (hM : 0<M) (hR : 0<R) (hWL : (W:ℤ)∣L) (hWM : (W:ℤ)∣(M:ℤ))
    (b : Label m) (hb : b∈(fullDomain X Xp W).image (expose L (M:ℤ) R))
    (E : Label m→Set (Fin m→ℤ)) :
    (jointLaw X Xp W hW hX hXp).real
        ({z | (fun j=>(z.1 j:ℤ))∈E (expose L (M:ℤ) R z)}∩
          ((fullDomain X Xp W).filter (fun z=>expose L (M:ℤ) R z=b):Set _)) /
      (jointLaw X Xp W hW hX hXp).real
        ((fullDomain X Xp W).filter (fun z=>expose L (M:ℤ) R z=b):Set _) =
    (jointLaw X Xp W hW hX hXp).real
        (jointFiber (E b) X Xp W b.scales b.residue L (b.left R) (b.width R) b.pivotResidue M:Set _) /
      (jointLaw X Xp W hW hX hXp).real
        (jointFiber Set.univ X Xp W b.scales b.residue L (b.left R) (b.width R) b.pivotResidue M:Set _) := by
  have hres := image_residues X Xp W L (M:ℤ) R hL (by exact_mod_cast hM) hWL hWM b hb
  have hc := fiber_eq X Xp W (fun j=>by have:=hX j; omega) L (M:ℤ) R hL
    (by exact_mod_cast hM) hR b hres.1 hres.2.1
  apply congrArg₂ (fun a b : ℝ=>a/b)
  · apply measureReal_congr
    filter_upwards [joint_ae_fullDomain X Xp W hW hX hXp] with z hz
    have hzr : z∈rawDomain X Xp W := (Finset.mem_filter.mp hz).1
    change ((fun j=>(z.1 j:ℤ))∈E (expose L (M:ℤ) R z) ∧
      z∈(fullDomain X Xp W).filter (fun z=>expose L (M:ℤ) R z=b)) =
        (z∈jointFiber (E b) X Xp W b.scales b.residue L (b.left R) (b.width R) b.pivotResidue M)
    apply propext
    rw [jointFiber_filter,←hc]
    simp only [Finset.mem_filter,hz,hzr,true_and]
    by_cases he : expose L (M:ℤ) R z=b <;> simp only [he,and_true,true_and,and_false,false_and]
  · apply measureReal_congr
    filter_upwards [joint_ae_fullDomain X Xp W hW hX hXp] with z hz
    have hzr : z∈rawDomain X Xp W := (Finset.mem_filter.mp hz).1
    change (z∈(fullDomain X Xp W).filter (fun z=>expose L (M:ℤ) R z=b)) =
        (z∈jointFiber Set.univ X Xp W b.scales b.residue L (b.left R) (b.width R) b.pivotResidue M)
    rw [←hc]
    simp only [Finset.mem_filter,hz,hzr,true_and]

end RoughFaceShift
end
end

section
noncomputable section
namespace RoughFaceShift
open RationalLattice MalcevCharacters RealPolynomialDegree RoughScales Filter
open RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open ProductExposureLabels ProductExposureLaw RawHarmonicProbability ProductExposureCutoff MeasureTheory
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

 

theorem source_raw_face_decay {G : Type} [Group G] [TopologicalSpace G] {dim : ℕ}
    (Γ : Subgroup G) [MetricSpace (G⧸Γ)] [IsTopologicalGroup G]
    (c : RealCoordinates G dim) (hsk : SecondKind c)
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (htop : (inferInstance : MetricSpace (G⧸Γ)).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace Γ)
    (m v D d : ℕ) (hd : 0<d) (c₀ C₀ : ℝ) (B K : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η)
    (w M Xp : ℕ→ℕ) (X : ℕ→Fin m→ℕ) (R H : ℕ→ℝ) (L : ℕ→ℤ)
    (hw : Tendsto w atTop atTop)
    (hX : ∀ n j,4*primorial (w n)≤X n j) (hXp : ∀ n,4*primorial (w n)≤Xp n)
    (hXt : ∀ j,Tendsto (fun n=>X n j) atTop atTop) (hXpt : Tendsto Xp atTop atTop)
    (hR : ∀ n,0<R n) (hRX : Tendsto (fun n=>R n/(Xp n:ℝ)) atTop (𝓝 0))
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun n=>(R n/(M n:ℝ))/
      (1+∑ j,(X n j:ℝ)^2)^a) atTop atTop)
    (hH : ∀ n,0≤H n) (hHZ : Tendsto (fun n=>H n/(R n/(M n:ℝ))) atTop (𝓝 0))
    (hWM : ∀ n,(primorial (w n):ℤ)∣(M n:ℤ))
    (hM : ∀ n,0<M n) (hMs : ∀ n,Smooth (w n) (M n:ℤ))
    (hL : ∀ n,0<L n) (hsm : ∀ n,Smooth (w n) (L n))
    (hWL : ∀ n,(primorial (w n):ℤ)∣L n)
    (hXL : ∀ j,Tendsto (fun n=>(X n j:ℝ)/(L n:ℝ)) atTop atTop)
    (F : ℕ→Label m→FaceData m v G Γ)
    (hF : ∀ n b,b∈(fullDomain (X n) (Xp n) (primorial (w n))).image
      (expose (L n) (M n:ℤ) (R n)) → Good (X n) (Xp n) (R n) b →
        FaceData.Valid c D d K (H n) (L n) b (F n b)) :
    Tendsto (fun n=>(jointLaw (X n) (Xp n) (primorial (w n)) (primorial_pos _)
      (hX n) (hXp n)).real (rawFaceEvent Γ m v c₀ C₀ B η (R n) d (M n) (L n) (F n)))
      atTop (𝓝 0)
 := by
  have hXpr (n : ℕ) : (0:ℝ)<Xp n := by
    have:=hXp n;have:=primorial_pos (w n);exact_mod_cast (show 0<Xp n by omega)
  have hMr (n : ℕ) : (0:ℝ)<M n := by exact_mod_cast hM n
  have hRsmall : ∀ᶠ n in atTop,2*R n≤(Xp n:ℝ) := by
    have hh := (tendsto_order.mp hRX).2 (1/2) (by norm_num)
    filter_upwards [hh] with n hn
    have := (div_lt_iff₀ (hXpr n)).mp hn
    linarith
  have hZtop : Tendsto (fun n=>R n/(M n:ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (fun n=>?_) (hZ 1 (by norm_num))
    rw [Real.rpow_one]
    exact div_le_self (div_nonneg (hR n).le (hMr n).le)
      (by have:=Finset.sum_nonneg (fun j (_ : j∈Finset.univ)=>sq_nonneg (X n j:ℝ));linarith)
  have hRmin : ∀ᶠ n in atTop,4*(M n:ℝ)*2^m≤R n := by
    filter_upwards [(tendsto_atTop.mp hZtop) (4*2^m)] with n hn
    have hh := (le_div_iff₀ (hMr n)).mp hn
    nlinarith
  have hUV : ∀ n j,(X n j:ℝ)≤(X n j:ℝ)^2 := by
    intro n j
    have h1 : (1:ℝ)≤X n j := by
      have:=hX n j;have:=primorial_pos (w n);exact_mod_cast (show 1≤X n j by omega)
    nlinarith
  have hu := source_raw_joint_face_uniform Γ c hsk hΓ htop m v D d hd c₀ C₀ B K η
    hc₀ hC₀ hB hη w M (fun n j=>(X n j:ℝ)) (fun n j=>(X n j:ℝ)^2)
    (fun n=>R n/(M n:ℝ)) H L hw
    (fun j=>tendsto_natCast_atTop_atTop.comp (hXt j)) hUV hZ hH hHZ hWM hM hMs
    hL hsm hWL hXL
  have hbad : Tendsto (fun n=>(jointLaw (X n) (Xp n) (primorial (w n)) (primorial_pos _)
      (hX n) (hXp n)).real {z | ¬Good (X n) (Xp n) (R n) (expose (L n) (M n:ℤ) (R n) z)})
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _=>measureReal_nonneg))
    · filter_upwards [hRsmall] with n hn
      exact bad_good_bound (X n) (Xp n) (primorial (w n)) (primorial_pos _) (hX n) (hXp n)
        (L n) (M n:ℤ) (R n) (hR n) (by linarith [hR n])
    · have ht := tendsto_finsetSum Finset.univ (fun j _=>
        raw_cutoff_decay (fun n=>X n j) (fun n=>primorial (w n)) 1
          (fun _=>primorial_pos _) (fun n=>hX n j) (hXt j))
      have hp := raw_cutoff_decay Xp (fun n=>primorial (w n)) (m+2)
        (fun _=>primorial_pos _) hXp hXpt
      simpa using ht.add hp
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _=>lt_of_lt_of_le ha measureReal_nonneg)
  · intro e he
    let ε := min (e/3) (1/2)
    have hε : 0<ε := lt_min (by linarith) (by norm_num)
    have hε1 : ε≤1 := (min_le_right _ _).trans (by norm_num)
    filter_upwards [hu ε hε,hRsmall,hRmin,(tendsto_order.mp hbad).2 (e/3) (by linarith)]
      with n hn hsmall hmin hbadn
    have hb := supported_conditional_bad_bound
      (jointLaw (X n) (Xp n) (primorial (w n)) (primorial_pos _) (hX n) (hXp n))
      (fullDomain (X n) (Xp n) (primorial (w n)))
      (joint_ae_fullDomain (X n) (Xp n) (primorial (w n)) (primorial_pos _) (hX n) (hXp n))
      (expose (L n) (M n:ℤ) (R n)) {b | Good (X n) (Xp n) (R n) b}
      (rawFaceEvent Γ m v c₀ C₀ B η (R n) d (M n) (L n) (F n)) ε hε.le hε1
      (by
        intro b hb hg
        have hlegal := label_exposure_legal (X n) (Xp n) (w n) (M n) (L n) (R n)
          (hX n) (hXp n) (hL n) (hM n) (hWL n) (hWM n) (hR n) hsmall hmin b hb hg
        have hres := image_residues (X n) (Xp n) (primorial (w n)) (L n) (M n:ℤ) (R n)
          (hL n) (by exact_mod_cast hM n) (hWL n) (hWM n) b hb
        have hv := hF n b hb hg
        have hpre := good_preimages (X n) (Xp n) (R n) (hR n).le (L n) (hL n) b hg
        have hlocal := hn (labelExposure b (R n) (M n)) hlegal (X n) (Xp n) (hX n) (hXp n)
          hres.2.2.2 (fun j=>(hg.1 j).1) (fun j=>(hg.1 j).2)
          (fun t ht=>(hpre t ht).1) (fun t ht=>(hpre t ht).2)
          (F n b).A (F n b).P hv.1 (F n b).σ hv.2.1 (F n b).h hv.2.2.1 hv.2.2.2
        have heq := label_conditional_exact (X n) (Xp n) (primorial (w n)) (M n) (L n) (R n)
          (primorial_pos _) (hX n) (hXp n) (hL n) (hM n) (hR n) (hWL n) (hWM n) b hb
          (fun b=>{t | badFace Γ m v c₀ C₀ B η (labelExposure b (R n) (M n)).Z d (M n)
            (F n b).A (F n b).P (F n b).σ t})
        exact heq.trans_le hlocal.le)
    have hεe : ε≤e/3 := min_le_left _ _
    change (jointLaw (X n) (Xp n) (primorial (w n)) (primorial_pos _) (hX n) (hXp n)).real
      (rawFaceEvent Γ m v c₀ C₀ B η (R n) d (M n) (L n) (F n)) ≤ ε+
      (jointLaw (X n) (Xp n) (primorial (w n)) (primorial_pos _) (hX n) (hXp n)).real
        {z | ¬Good (X n) (Xp n) (R n) (expose (L n) (M n:ℤ) (R n) z)} at hb
    change _<e/3 at hbadn
    linarith

end RoughFaceShift
end
end

section
noncomputable section
namespace RoughCoveredFace
open RoughFaceShift RationalLattice MalcevCharacters RealPolynomialDegree RoughScales Filter
open RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open scoped BigOperators Topology
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {dim : ℕ}
variable (c : RealCoordinates G dim) (Γ : Subgroup G) [mtr : MetricSpace (G⧸Γ)]

theorem source_product_cover_decay (Λ : Subgroup G) (hle : Λ≤Γ) (hsk : SecondKind c)
    (hΛ : ∀ g : G,g∈Λ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (htop : (inferInstance : MetricSpace (G⧸Γ)).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace Γ)
    (m v D d : ℕ) (hd : 0<d) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η)
    (w M : ℕ→ℕ) (S : ℕ → Fin m → ℝ) (Z : ℕ→ℝ)
    (r : ℕ → Fin m → ℤ) (L : ℕ→ℤ)
    (hw : Tendsto w atTop atTop) (hS : ∀ j,Tendsto (fun n=>S n j) atTop atTop)
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun n=>Z n/(1+∑ j,S n j)^a) atTop atTop)
    (hM : ∀ n,0<M n) (hMs : ∀ n,Smooth (w n) (M n:ℤ))
    (hL : ∀ n,0<L n) (hsm : ∀ n,Smooth (w n) (L n))
    (hWL : ∀ n,(primorial (w n):ℤ)∣L n)
    (hr : ∀ n j,(r n j).natAbs.Coprime (primorial (w n)))
    (hSL : ∀ j,Tendsto (fun n=>S n j/(L n:ℝ)) atTop atTop) :
    ∀ ε : ℝ,0<ε →∀ᶠ n in atTop,
      ∀ (A : Fin v → ℤ) (P : (Fin (m+v)→ℝ)→G),
      (∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D) →
      ((exceptionalProduct Γ m v c₀ C₀ B η (Z n) d (M n) A P (S n) (r n) (L n)).card:ℝ)/
        ((productTimes (S n) (r n) (L n)).card:ℝ)<ε := by
  classical
  let : MetricSpace (G⧸Λ) := coordinateQuotientMetric c Λ hΛ
  let V : @Homeomorph (G⧸Γ) (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ)
      mtr.toUniformSpace.toTopologicalSpace :=
    @Homeomorph.mk _ _ (QuotientGroup.instTopologicalSpace Γ)
      mtr.toUniformSpace.toTopologicalSpace (Equiv.refl _) (by rw [htop];exact @continuous_id (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ))
        (by rw [htop];exact @continuous_id (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ))
  obtain ⟨K,hK⟩ := RoughCoverTests.uniform_cover_tests c Λ Γ hΛ hle V B B (η/4) B.2 (by positivity)
  let η₀ : NNReal := ⟨η/4,by positivity⟩
  let B' : NNReal := K+B+η₀+1
  have hKB : K≤B' := by dsimp [B'];nlinarith [B.2,η₀.2]
  have hBB : (B:ℝ)+η/4≤B' := by
    change (B:ℝ)+η/4≤(K:ℝ)+B+(η₀:ℝ)+1
    change (B:ℝ)+η/4≤(K:ℝ)+B+η/4+1
    linarith [K.2]
  have hB' : 0<B' := by dsimp [B'];positivity
  intro ε hε
  have hp := source_product_decay c Λ hsk hΛ (coordinateQuotientMetric_topology c Λ hΛ)
    m v D d hd c₀ C₀ B' (η/2) hc₀ hC₀ hB' (by positivity) w M S Z r L
    hw hS hZ hM hMs hL hsm hWL hr hSL ε hε
  filter_upwards [hp] with n hn
  intro A P hP
  have hsub : exceptionalProduct Γ m v c₀ C₀ B η (Z n) d (M n) A P (S n) (r n) (L n) ⊆
      exceptionalProduct Λ m v c₀ C₀ B' (η/2) (Z n) d (M n) A P (S n) (r n) (L n) := by
    intro t ht
    obtain ⟨ht,lo,hi,res,F,hside,hbox,hF,hbound,hdisc⟩ := Finset.mem_filter.mp ht
    obtain ⟨g,hg,hgb,herr⟩ := hK F hF hbound
    apply Finset.mem_filter.mpr
    refine ⟨ht,lo,hi,res,g,hside,hbox,hg.weaken hKB,fun y=>(hgb y).trans hBB,?_⟩
    have he := herr (Fin v→ℤ) (physicalResidueBox lo hi res d)
      (nestedBox lo hi res A d (M n) (∏ j,t j))
      (fun x=>P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))) η hdisc
    linarith
  exact (div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub)
    (Nat.cast_nonneg _)).trans_lt (hn A P hP)

end RoughCoveredFace

end
end

end OAI
