import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughCovered01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
noncomputable section
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
      ∀ (σ : (G⧸Γ) → (G⧸Γ)),LipschitzWith K σ →
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

 
theorem source_raw_joint_face_uniform (Λ : Subgroup G) (hle : Λ≤Γ) (hsk : SecondKind c)
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
    (hWM : ∀ n,(primorial (w n):ℤ)∣(M n:ℤ))
    (hM : ∀ n,0<M n) (hMs : ∀ n,Smooth (w n) (M n:ℤ))
    (hL : ∀ n,0<L n) (hsm : ∀ n,Smooth (w n) (L n))
    (hWL : ∀ n,(primorial (w n):ℤ)∣L n)
    (hUL : ∀ j,Tendsto (fun n=>U n j/(L n:ℝ)) atTop atTop) :
    ∀ ε : ℝ,0<ε →∀ᶠ n in atTop,
      ∀ b : Exposure m,b.Legal (U n) (V n) (Z0 n) (w n) (M n) →
      ∀ (X : Fin m→ℕ) (Xp : ℕ) (hX : ∀ j,4*primorial (w n)≤X j)
        (hXp : 4*primorial (w n)≤Xp),b.a.natAbs.Coprime (primorial (w n)) →
      (∀ j,(X j:ℝ)≤b.S j) → (∀ j,2*b.S j≤(X j:ℝ)^2) →
      (∀ t∈productTimes b.S b.r (L n),(Xp:ℝ)≤b.Q/(∏ j,(t j:ℝ))) →
      (∀ t∈productTimes b.S b.r (L n),(b.Q+b.Δ)/(∏ j,(t j:ℝ))≤(Xp:ℝ)^2) →
      ∀ (A : Fin v → ℤ) (P : (Fin (m+v)→ℝ)→G),
      (∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D) →
      ∀ (σ : (G⧸Γ) → (G⧸Γ)),LipschitzWith K σ →
      ∀ h : (Fin m → ℤ) → Fin v → ℤ,
      (∀ t∈productTimes b.S b.r (L n),∀ i,(d:ℤ)∣h t i ∧ |(h t i:ℝ)|≤H n) →
      (∀ t∈productTimes b.S b.r (L n),∀ x : Fin v → ℤ,
        σ (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))=
          QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>((x i+h t i:ℤ):ℝ))))) →
      (ProductExposureLaw.jointLaw X Xp (primorial (w n)) (primorial_pos _) hX hXp).real
        (ProductExposureLaw.jointFiber
          {t | badFace Γ m v c₀ C₀ B η b.Z d (M n) A P σ t}
          X Xp (primorial (w n)) b.S b.r (L n) b.Q b.Δ b.a (M n) : Set _) /
      (ProductExposureLaw.jointLaw X Xp (primorial (w n)) (primorial_pos _) hX hXp).real
        (ProductExposureLaw.jointFiber Set.univ
          X Xp (primorial (w n)) b.S b.r (L n) b.Q b.Δ b.a (M n) : Set _) < ε
 := by
  classical
  intro ε hε
  have hu := raw_conditional_face_uniform (Γ:=Γ) (c:=c) Λ hle hsk hΛ htop m v D d hd
    c₀ C₀ B K η hc₀ hC₀ hB hη w M U V Z0 H L hw hU hUV hZ hH hHZ
    hM hMs hL hsm hWL hUL ε hε
  filter_upwards [hu] with n hn
  intro b hb X Xp hX hXp ha hloD hhiD hloP hhiP A P hP σ hσ h hh hid
  rw [ProductExposureLaw.conditional_exact,
    HarmonicExposure.literal_mass_eq _ X Xp _ b.S b.r (L n) b.Q b.Δ b.a (M n)
      (hL n) (hWL n) hb.2.2.1 hloD hhiD,
    HarmonicExposure.literal_mass_eq Set.univ X Xp _ b.S b.r (L n) b.Q b.Δ b.a (M n)
      (hL n) (hWL n) hb.2.2.1 hloD hhiD]
  simpa only [exceptionalFace,Set.mem_ofPred_eq,Set.mem_univ,Finset.filter_true_of_mem (fun _ _=>True.intro)] using
    hn b hb Xp (primorial (w n)) (hWM n) ha hloP hhiP A P hP σ hσ h hh hid

end RoughCoveredFace
end

end
end

section
noncomputable section
namespace RoughCoveredFace
open RoughFaceShift
open RationalLattice MalcevCharacters RealPolynomialDegree RoughScales Filter
open RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open ProductExposureLabels ProductExposureLaw RawHarmonicProbability ProductExposureCutoff MeasureTheory
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

 

theorem source_raw_face_cover_decay {G : Type} [Group G] [TopologicalSpace G] {dim : ℕ}
    (Λ Γ : Subgroup G) [MetricSpace (G⧸Γ)] [IsTopologicalGroup G]
    (c : RealCoordinates G dim) (hsk : SecondKind c)
    (hle : Λ≤Γ) (hΛ : ∀ g : G,g∈Λ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
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
  have hu := source_raw_joint_face_uniform Γ c Λ hle hsk hΛ htop m v D d hd c₀ C₀ B K η
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

end RoughCoveredFace

end
end

end OAI
