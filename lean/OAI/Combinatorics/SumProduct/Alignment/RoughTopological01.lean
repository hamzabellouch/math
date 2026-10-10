import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughCovered02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
noncomputable section
end
end

section
noncomputable section
namespace RoughCoveredFace
open RationalLattice MalcevCharacters RealPolynomialDegree

 

theorem grid_second_degree_cover {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {dim : ℕ} (c : RealCoordinates G dim) (Γ : Subgroup G)
    (grid : ℕ) (hgridpos : 0<grid)
    (hgrid : ∀ g : G,(∀ i,∃ z : ℤ,c.coord g i=(grid:ℝ)*z) → g∈Γ) :
    ∃ Λ : Subgroup G,∃ e : RealCoordinates G dim,SecondKind e ∧
      (∀ g : G,g∈Λ ↔ ∀ i,∃ z : ℤ,e.coord g i=z) ∧ Λ≤Γ ∧
      ∃ E : ℕ,0<E ∧ ∀ v D : ℕ,∀ P : (Fin v→ℝ)→G,
        (∀ i,HasDegree (fun x=>canonicalLog c (P x) i) D) →
        ∀ i,HasDegree (fun x=>canonicalLog e (P x) i) (E*D) := by
  classical
  obtain ⟨w,hw,hgw,hcl⟩:=exists_lattice_weights c grid hgridpos
  let Λ:=weightedLattice c w hcl
  let d:=scaledCoordinates c w hw
  have hΛ : ∀ g : G,g∈Λ ↔ ∀ i,∃ z : ℤ,d.coord g i=z :=
    weightedLattice_iff c w hcl hw
  have hle : Λ≤Γ := by
    intro g hg
    apply hgrid g
    intro i
    obtain ⟨a,ha⟩:=hg i
    obtain ⟨b,hb⟩:=hgw i
    refine ⟨(b:ℤ)*a,?_⟩
    rw [ha,hb]
    push_cast
    ring
  let e:=secondCoordinates d
  have he : ∀ i,RationalPolynomialMap.IsPolynomial
      (fun x : Fin dim→ℝ=>e.coord (c.coord.symm x) i) := by
    intro i
    apply polynomial_expCoordinates d
    intro j
    change RationalPolynomialMap.IsPolynomial
      (fun x : Fin dim→ℝ=>c.coord (c.coord.symm x) j/(w j:ℝ))
    simpa only [Homeomorph.apply_symm_apply,div_eq_mul_inv,Rat.cast_inv,Rat.cast_natCast] using
      RationalPolynomialMap.mul (RationalPolynomialMap.coordinate j)
        (RationalPolynomialMap.const (w j:ℚ)⁻¹)
  obtain ⟨C,hC,hcoord⟩:=coord_degree_bound c
  obtain ⟨L,hL,hlog⟩:=log_degree_bound e
  obtain ⟨T,hT,htransfer⟩:=rational_map_bound (fun i x=>e.coord (c.coord.symm x) i) he
  refine ⟨Λ,e,secondCoordinates_secondKind d,expCoordinates_lattice d Λ hΛ,hle,
    L*(T*C),Nat.mul_pos hL (Nat.mul_pos hT hC),?_⟩
  intro v D P hP i
  have hc:=hcoord v D P hP
  have ht : ∀ j,HasDegree (fun x=>e.coord (P x) j) (T*(C*D)) := by
    intro j
    simpa only [Homeomorph.symm_apply_apply] using
      htransfer v (C*D) (fun j x=>c.coord (P x) j) hc j
  simpa only [Nat.mul_assoc] using hlog v (T*(C*D)) P ht i

end RoughCoveredFace
end
end

section

section
noncomputable section
namespace RoughCoveredFace
open RoughFaceShift
open RationalLattice MalcevCharacters RealPolynomialDegree RoughScales Filter
open RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open ProductExposureLabels ProductExposureLaw ProductExposureCutoff MeasureTheory
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
 

theorem source_raw_face_grid_decay {G : Type} [Group G] [TopologicalSpace G] {dim : ℕ}
    (Γ : Subgroup G) [MetricSpace (G⧸Γ)] [IsTopologicalGroup G]
    (c : RealCoordinates G dim) (grid : ℕ) (hgridpos : 0<grid)
    (hgrid : ∀ g : G,(∀ i,∃ z : ℤ,c.coord g i=(grid:ℝ)*z) → g∈Γ)
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
  obtain ⟨Λ,e,he,hΛ,hle,E,hE,hdeg⟩:=grid_second_degree_cover c Γ grid hgridpos hgrid
  apply source_raw_face_cover_decay Λ Γ e he hle hΛ htop m v (E*D) d hd c₀ C₀ B K η
    hc₀ hC₀ hB hη w M Xp X R H L hw hX hXp hXt hXpt hR hRX hZ hH hHZ
    hWM hM hMs hL hsm hWL hXL F
  intro n b hb hg
  obtain ⟨hP,hσ,hh,hface⟩:=hF n b hb hg
  exact ⟨hdeg (m+v) D (F n b).P hP,hσ,hh,hface⟩

end RoughCoveredFace
end
end
end

section
 
noncomputable section
namespace RoughTopologicalFace
open RoughFaceShift RationalLattice MalcevCharacters RealPolynomialDegree RoughProductRemoval
 

def TopologicalValid {m v : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    {Γ : Subgroup G} [MetricSpace (G⧸Γ)] {dim : ℕ} (c : RealCoordinates G dim)
    (D d : ℕ) (H : ℝ) (L : ℤ) (b : ProductExposureLabels.Label m)
    (σ₀ : C(G⧸Γ,G⧸Γ)) (F : FaceData m v G Γ) : Prop :=
  (∀ i,HasDegree (fun y=>canonicalLog c (F.P y) i) D) ∧
  F.σ=σ₀ ∧
  (∀ t∈productTimes b.scales b.residue L,∀ i,(d:ℤ)∣F.h t i ∧ |(F.h t i:ℝ)|≤H) ∧
  (∀ t∈productTimes b.scales b.residue L,∀ x : Fin v→ℤ,
    F.σ (QuotientGroup.mk (F.P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))=
      QuotientGroup.mk (F.P (Fin.append (fun j=>(t j:ℝ)) (fun i=>((x i+F.h t i:ℤ):ℝ)))))
end RoughTopologicalFace
end

end

section
 
noncomputable section
namespace RoughTopologicalFace
open RoughFaceShift RationalLattice MalcevCharacters RealPolynomialDegree RoughProductRemoval
open FinitePieceAverages
open scoped BigOperators Topology

 

def Approximable {X : Type*} [MetricSpace X] (B K : NNReal) (η : ℝ)
    (σ : X→X) : Prop :=
  ∀ f : X→ℂ,LipschitzWith B f → (∀ x,‖f x‖≤B) →
    ∃ g : X→ℂ,LipschitzWith K g ∧ (∀ x,‖g x‖≤K) ∧
      ∀ x,‖f (σ x)-g x‖≤η/8

 

theorem continuous_approximable {X : Type} [MetricSpace X] [CompactSpace X]
    [Nonempty X] (σ : C(X,X)) (B : NNReal) (η : ℝ) (hη : 0<η) :
    ∃ K : NNReal,Approximable B K η σ := by
  let H : C(PUnit.{1}×X,X):=σ.comp ContinuousMap.snd
  obtain ⟨L,hL⟩:=UniformLipschitzApproximation.compact_pullback_complex
    H B B B.2 (η/8) (by positivity)
  let e : NNReal:=⟨η/8,by positivity⟩
  let K : NNReal:=L+B+e+1
  have hLK : L≤K := by
    change (L:ℝ)≤(L:ℝ)+(B:ℝ)+η/8+1
    linarith [B.2]
  have hBK : (B:ℝ)+η/8≤(K:ℝ) := by
    change (B:ℝ)+η/8≤(L:ℝ)+(B:ℝ)+η/8+1
    linarith [L.2]
  refine ⟨K,?_⟩
  intro f hf hB
  obtain ⟨g,hg,herr,hgB⟩:=hL PUnit.unit f hf hB
  refine ⟨g,hg.weaken hLK,fun x=>(hgB x).trans hBK,?_⟩
  intro x
  rw [norm_sub_rev]
  simpa only [H,ContinuousMap.comp_apply,ContinuousMap.snd_apply] using (herr x).le

 

theorem Approximable.compare {X α : Type*} [MetricSpace X] {B K : NNReal}
    {η : ℝ} {σ : X→X} (hσ : Approximable B K η σ) (hη : 0<η)
    (S T : Finset α) (P : α→X)
    (hcompare : ∀ g : X→ℂ,LipschitzWith K g → (∀ x,‖g x‖≤K) →
      ‖mean S (fun x=>g (P x))-mean T (fun x=>g (P x))‖<η/4)
    (f : X→ℂ) (hf : LipschitzWith B f) (hfB : ∀ x,‖f x‖≤B) :
    ‖mean S (fun x=>f (σ (P x)))-mean T (fun x=>f (σ (P x)))‖<η/2 := by
  obtain ⟨g,hg,hgB,herr⟩:=hσ f hf hfB
  have hS:=mean_error S (fun x=>f (σ (P x))) (fun x=>g (P x))
    (η/8) (by positivity) (fun x _=>herr (P x))
  have hT:=mean_error T (fun x=>f (σ (P x))) (fun x=>g (P x))
    (η/8) (by positivity) (fun x _=>herr (P x))
  have hmid:=hcompare g hg hgB
  have htri:=norm_sub_le_norm_sub_add_norm_sub
    (mean S (fun x=>f (σ (P x)))) (mean S (fun x=>g (P x)))
    (mean T (fun x=>f (σ (P x))))
  have htri':=norm_sub_le_norm_sub_add_norm_sub
    (mean S (fun x=>g (P x))) (mean T (fun x=>g (P x)))
    (mean T (fun x=>f (σ (P x))))
  rw [norm_sub_rev (mean T (fun x=>g (P x)))] at htri'
  linarith

 
def ApproxValid {m v : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    {Γ : Subgroup G} [MetricSpace (G⧸Γ)] {dim : ℕ} (c : RealCoordinates G dim)
    (D d : ℕ) (B K : NNReal) (η H : ℝ) (L : ℤ) (b : ProductExposureLabels.Label m)
    (F : FaceData m v G Γ) : Prop :=
  (∀ i,HasDegree (fun y=>canonicalLog c (F.P y) i) D) ∧
  Approximable B K η F.σ ∧
  (∀ t∈productTimes b.scales b.residue L,∀ i,(d:ℤ)∣F.h t i ∧ |(F.h t i:ℝ)|≤H) ∧
  (∀ t∈productTimes b.scales b.residue L,∀ x : Fin v→ℤ,
    F.σ (QuotientGroup.mk (F.P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))=
      QuotientGroup.mk (F.P (Fin.append (fun j=>(t j:ℝ)) (fun i=>((x i+F.h t i:ℤ):ℝ)))))

end RoughTopologicalFace
end

end

section
 

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
      ∀ (σ : (G⧸Γ) → (G⧸Γ)),Approximable B K η σ →
      ∀ h : (Fin m → ℤ) → Fin v → ℤ,
      (∀ t∈productTimes (S n) (r n) (L n),∀ i,(d:ℤ)∣h t i ∧ |(h t i:ℝ)|≤H n) →
      (∀ t∈productTimes (S n) (r n) (L n),∀ x : Fin v → ℤ,
        σ (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))=
          QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>((x i+h t i:ℤ):ℝ))))) →
      ((exceptionalFace Γ m v c₀ C₀ B η (Z n) d (M n) A P σ (S n) (r n) (L n)).card:ℝ)/
        ((productTimes (S n) (r n) (L n)).card:ℝ)<ε := by
  classical
  let B' : NNReal := B+K+1
  have hB' : 0<B' := by
    change (0:ℝ)<(B:ℝ)+(K:ℝ)+1
    linarith [B.2,K.2]
  have hBB : B≤B' := by
    change (B:ℝ)≤(B:ℝ)+(K:ℝ)+1
    linarith [K.2]
  have hKB : K≤B' := by
    change (K:ℝ)≤(B:ℝ)+(K:ℝ)+1
    linarith [B.2]
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
    have hface := hσ.compare hη (physicalResidueBox lo hi res d)
      (nestedBox lo hi res A d (M n) (∏ j,t j))
      (fun x=>QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))
      (fun g hg hgB=>hcompare g (hg.weaken hKB)
        (fun y=>(hgB y).trans (by exact_mod_cast hKB))) test hLip hnorm
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
    change ‖Y-X‖<η/2 at hface
    rw [norm_sub_rev] at hface
    change ‖Y-U‖<η/4 at hsmall
    linarith
  exact (div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub)
    (Nat.cast_nonneg _)).trans_lt (hpn A P hP)

end RoughTopologicalFace

end
end
end

end OAI
