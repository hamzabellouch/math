import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.ProductExposure03
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
open ProductExposureLabels ProductExposureLaw MeasureTheory
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

 
def fullDomain {m : ℕ} (X : Fin m→ℕ) (Xp W : ℕ) : Finset ((Fin m→ℕ)×ℕ) :=
  (rawDomain X Xp W).filter (fun z=>W.Coprime z.2)

def labelExposure {m : ℕ} (b : Label m) (R : ℝ) (M : ℕ) : Exposure m where
  S := b.scales
  r := b.residue
  Z := b.width R / (M:ℝ)
  Q := b.left R
  Δ := b.width R
  a := b.pivotResidue

structure FaceData (m v : ℕ) (G : Type) [Group G] (Γ : Subgroup G) where
  A : Fin v→ℤ
  P : (Fin (m+v)→ℝ)→G
  σ : (G⧸Γ)→(G⧸Γ)
  h : (Fin m→ℤ)→Fin v→ℤ

def FaceData.Valid {m v : ℕ} {G : Type} [Group G] [TopologicalSpace G] {Γ : Subgroup G}
    [MetricSpace (G⧸Γ)] {dim : ℕ} (c : RealCoordinates G dim) (D d : ℕ)
    (K : NNReal) (H : ℝ) (L : ℤ) (b : Label m) (F : FaceData m v G Γ) : Prop :=
  (∀ i,HasDegree (fun y=>canonicalLog c (F.P y) i) D) ∧
  LipschitzWith K F.σ ∧
  (∀ t∈productTimes b.scales b.residue L,∀ i,(d:ℤ)∣F.h t i ∧ |(F.h t i:ℝ)|≤H) ∧
  (∀ t∈productTimes b.scales b.residue L,∀ x : Fin v→ℤ,
    F.σ (QuotientGroup.mk (F.P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))=
      QuotientGroup.mk (F.P (Fin.append (fun j=>(t j:ℝ)) (fun i=>((x i+F.h t i:ℤ):ℝ)))))

def rawFaceEvent {G : Type} [Group G] (Γ : Subgroup G) [MetricSpace (G⧸Γ)]
    (m v : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η R : ℝ) (d M : ℕ) (L : ℤ)
    (F : Label m→FaceData m v G Γ) : Set ((Fin m→ℕ)×ℕ) :=
  {z | let b:=expose L (M:ℤ) R z
       badFace Γ m v c₀ C₀ B η ((labelExposure b R M).Z) d M
         (F b).A (F b).P (F b).σ (fun j=>(z.1 j:ℤ))}

end RoughFaceShift
end
end

section
noncomputable section
namespace RoughFaceShift
open ProductExposureLabels ProductExposureLaw RawHarmonicProbability MeasureTheory
open RoughSamplingWeights RoughSourceExceptional RoughProductRemoval
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

lemma joint_ae_fullDomain {m : ℕ} (X : Fin m→ℕ) (Xp W : ℕ) (hW : 0<W)
    (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp) :
    ∀ᵐ z ∂jointLaw X Xp W hW hX hXp,z∈fullDomain X Xp W := by
  have hp : ∀ᵐ z ∂jointLaw X Xp W hW hX hXp,z.2∈units Xp W := by
    rw [ae_iff,←measureReal_eq_zero_iff]
    change (jointLaw X Xp W hW hX hXp).real {z | z.2∈(units Xp W:Set ℕ)ᶜ}=0
    rw [pivot_marginal]
    exact (measureReal_eq_zero_iff (by finiteness)).mpr
      (ae_iff.mp (law_ae_units Xp W hW hXp))
  filter_upwards [joint_ae_domain X Xp W hW hX hXp,hp] with z hz hp
  exact Finset.mem_filter.mpr ⟨hz,(Finset.mem_filter.mp hp).2⟩

lemma joint_restrict_fullDomain {m : ℕ} (X : Fin m→ℕ) (Xp W : ℕ) (hW : 0<W)
    (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp) (A : Set ((Fin m→ℕ)×ℕ)) :
    (jointLaw X Xp W hW hX hXp).real (A∩(fullDomain X Xp W:Set _)) =
      (jointLaw X Xp W hW hX hXp).real A := by
  apply measureReal_congr
  filter_upwards [joint_ae_fullDomain X Xp W hW hX hXp] with z hz
  change (z∈A ∧ z∈fullDomain X Xp W)=(z∈A)
  exact propext ⟨And.left,fun ha=>⟨ha,hz⟩⟩

lemma emod_unit (W t : ℕ) (L : ℤ) (hWL : (W:ℤ)∣L) (ht : W.Coprime t) :
    ((t:ℤ)%L).natAbs.Coprime W := by
  obtain ⟨k,hk⟩ := hWL
  have hc : IsCoprime (t:ℤ) (W:ℤ) := Int.isCoprime_iff_nat_coprime.mpr (by simpa using ht.symm)
  have hd := hc.add_mul_left_left (-k*((t:ℤ)/L))
  have he : (t:ℤ)+(W:ℤ)*(-k*((t:ℤ)/L))=(t:ℤ)%L := by
    calc
      _ = (t:ℤ)-((t:ℤ)/L)*L := by rw [hk]; ring
      _ = (t:ℤ)%L := by have hh := Int.emod_add_ediv_mul (t:ℤ) L; linarith
  rw [he] at hd
  simpa only [Int.natAbs_natCast] using Int.isCoprime_iff_nat_coprime.mp hd

lemma image_residues {m : ℕ} (X : Fin m→ℕ) (Xp W : ℕ) (L M : ℤ) (R : ℝ)
    (hL : 0<L) (hM : 0<M) (hWL : (W:ℤ)∣L) (hWM : (W:ℤ)∣M)
    (b : Label m) (hb : b∈(fullDomain X Xp W).image (expose L M R)) :
    (∀ j,0≤b.residue j ∧ b.residue j<L) ∧
    (0≤b.pivotResidue ∧ b.pivotResidue<M) ∧
    (∀ j,(b.residue j).natAbs.Coprime W) ∧ b.pivotResidue.natAbs.Coprime W := by
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hraw,hp⟩ := Finset.mem_filter.mp hz
  have ht : ∀ j,z.1 j∈units (X j) W := by
    have hh : (∀ j,z.1 j∈units (X j) W) ∧ z.2∈Finset.Ico Xp (Xp^2) := by
      simpa only [rawDomain,Finset.product_eq_sprod,Finset.mem_product,Fintype.mem_piFinset] using hraw
    exact hh.1
  refine ⟨fun j=>⟨Int.emod_nonneg _ hL.ne',Int.emod_lt_of_pos _ hL⟩,
    ⟨Int.emod_nonneg _ hM.ne',Int.emod_lt_of_pos _ hM⟩,?_,?_⟩
  · intro j
    exact emod_unit W (z.1 j) L hWL (Finset.mem_filter.mp (ht j)).2
  · exact emod_unit W z.2 M hWM hp

lemma label_exposure_legal {m : ℕ} (X : Fin m→ℕ) (Xp w M : ℕ) (L : ℤ) (R : ℝ)
    (hX : ∀ j,4*primorial w≤X j) (_ : 4*primorial w≤Xp)
    (hL : 0<L) (hM : 0<M) (hWL : (primorial w:ℤ)∣L)
    (hWM : (primorial w:ℤ)∣(M:ℤ)) (hR : 0<R) (hRX : 2*R≤Xp)
    (hRmin : 4*(M:ℝ)*2^m≤R) (b : Label m)
    (hb : b∈(fullDomain X Xp (primorial w)).image (expose L (M:ℤ) R))
    (hg : Good X Xp R b) :
    (labelExposure b R M).Legal (fun j=>(X j:ℝ)) (fun j=>(X j:ℝ)^2)
      (R/(M:ℝ)) w M := by
  have hW := primorial_pos w
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hspos : ∀ j,0<b.scales j := fun j=>pow_pos (by norm_num) _
  have hprodpos : 0<∏ j,b.scales j := Finset.prod_pos (fun j _=>hspos j)
  have hsone : ∀ j,1≤b.scales j := by
    intro j
    have hx : (1:ℝ)≤X j := by have:=hX j; exact_mod_cast (show 1≤X j by omega)
    exact hx.trans (hg.1 j).1
  have hprod : (1:ℝ)≤∏ j,b.scales j := Finset.one_le_prod₀ (fun j _=>hsone j)
  have hwidth : 0<b.width R := b.width_pos R hR
  have hres := image_residues X Xp (primorial w) L (M:ℤ) R hL
    (by exact_mod_cast hM) hWL hWM b hb
  obtain ⟨z,hz,hb⟩ := Finset.mem_image.mp hb
  have hraw := (Finset.mem_filter.mp hz).1
  have hzraw : (∀ j,z.1 j∈units (X j) (primorial w)) ∧ z.2∈Finset.Ico Xp (Xp^2) := by
    simpa only [rawDomain,Finset.product_eq_sprod,Finset.mem_product,Fintype.mem_piFinset] using hraw
  have htpos : ∀ j,0<z.1 j := by
    intro j
    have:=hX j
    have: X j≤z.1 j := (Finset.mem_Ico.mp (Finset.mem_filter.mp (hzraw.1 j)).1).1
    omega
  have hbounds := expose_bounds L (M:ℤ) R hR z htpos
  rw [hb] at hbounds
  have htp := (product_dyadic_bounds b z.1 hbounds.1).1
  have hp : (Xp:ℝ)≤z.2 := by exact_mod_cast (Finset.mem_Ico.mp hzraw.2).1
  have hp0 : (0:ℝ)≤z.2 := by positivity
  have hmul : (∏ j,b.scales j)*(Xp:ℝ)≤(∏ j,(z.1 j:ℝ))*(z.2:ℝ) :=
    mul_le_mul htp hp (Nat.cast_nonneg _) (hprodpos.le.trans htp)
  have hΔQ : b.width R≤b.left R := by
    have hh := mul_le_mul_of_nonneg_left hRX hprodpos.le
    dsimp [Label.width] at hbounds ⊢
    nlinarith [hbounds.2.2]
  dsimp only [Exposure.Legal,labelExposure]
  refine ⟨?_,?_,hres.2.2.1,hwidth.trans_le hΔQ,hwidth,hΔQ,?_⟩
  · intro j
    exact ⟨(hg.1 j).1,by nlinarith [(hg.1 j).2,hspos j]⟩
  · apply div_le_div_of_nonneg_right _ hMr.le
    change R≤(∏ j,b.scales j)*R
    nlinarith [mul_le_mul_of_nonneg_right hprod hR.le]
  · change 4*(M:ℝ)*(2^m*∏ j,b.scales j)≤(∏ j,b.scales j)*R
    nlinarith [mul_le_mul_of_nonneg_left hRmin hprodpos.le]

lemma good_preimages {m : ℕ} (X : Fin m→ℕ) (Xp : ℕ) (R : ℝ) (hR : 0≤R)
    (L : ℤ) (hL : 0<L) (b : Label m) (hg : Good X Xp R b)
    (t : Fin m→ℤ) (ht : t∈productTimes b.scales b.residue L) :
    (Xp:ℝ)≤b.left R/(∏ j,(t j:ℝ)) ∧
    (b.left R+b.width R)/(∏ j,(t j:ℝ))≤(Xp:ℝ)^2 := by
  have hs : ∀ j,0<b.scales j := fun j=>pow_pos (by norm_num) _
  have hb : ∀ j,b.scales j≤(t j:ℝ) ∧ (t j:ℝ)<2*b.scales j := by
    intro j
    have hh := (mem_times (b.scales j) (b.residue j) L (t j) hL).mp
      (Fintype.mem_piFinset.mp ht j)
    exact ⟨hh.1,hh.2.1⟩
  have hlo : (∏ j,b.scales j)≤∏ j,(t j:ℝ) :=
    Finset.prod_le_prod₀ (fun j _=>(hs j).le) (fun j _=>(hb j).1)
  have hhi : (∏ j,(t j:ℝ))≤2^m*∏ j,b.scales j := by
    calc
      _ ≤ ∏ j,2*b.scales j := Finset.prod_le_prod₀ (fun j _=>(hs j).le.trans (hb j).1)
        (fun j _=>(hb j).2.le)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hh := hg.2 _ hlo hhi
  constructor <;> linarith [hh.1,hh.2]

end RoughFaceShift
end
end

section
noncomputable section
namespace RoughFaceShift
open Finset MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma real_support_restrict {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : Finset α) (hS : ∀ᵐ x ∂μ,x∈S) (A : Set α) : μ.real (A∩(S:Set α))=μ.real A := by
  apply measureReal_congr
  filter_upwards [hS] with x hx
  change (x∈A ∧ x∈S)=(x∈A)
  exact propext ⟨And.left,fun h=>⟨h,hx⟩⟩

lemma singleton_event_sum {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [SigmaFinite μ] (S : Finset α) (A : Set α) :
    (∑ x∈S,if x∈A then μ.real {x} else 0)=μ.real (A∩(S:Set α)) := by
  rw [←sum_filter, sum_measureReal_singleton]
  congr 1
  ext x
  simp only [mem_coe,mem_filter,Set.mem_inter_iff]
  exact and_comm

 

lemma supported_partition_lower {α ι : Type*} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (S : Finset α) (hS : ∀ᵐ x ∂μ,x∈S) (π : α→ι) (G : Set ι) (A : Set α)
    (a δ : ℝ) (ha : 0≤a) (hbad : μ.real {x | π x∉G}≤δ)
    (hc : ∀ b∈S.image π,b∈G → a*μ.real (S.filter (fun x=>π x=b):Set α)≤
      μ.real (A∩(S.filter (fun x=>π x=b):Set α))) :
    a*(1-δ)≤μ.real A := by
  classical
  have htotal : (∑ x∈S,μ.real {x})=1 := by
    rw [sum_measureReal_singleton]
    have hh := real_support_restrict μ S hS Set.univ
    simpa only [Set.univ_inter,probReal_univ] using hh
  have hbad' : (∑ x∈S.filter (fun x=>π x∉G),μ.real {x})≤δ*(∑ x∈S,μ.real {x}) := by
    have he : (S.filter (fun x=>π x∉G):Set α)={x | π x∉G}∩(S:Set α) := by
      ext x
      simp only [mem_coe,mem_filter,Set.mem_inter_iff,Set.mem_ofPred_eq]
      exact and_comm
    rw [sum_measureReal_singleton,he,real_support_restrict μ S hS,htotal,mul_one]
    exact hbad
  have hs (b : ι) (hb : b∈S.image π) (hG : b∈G) :
      a*(∑ x∈S.filter (fun x=>π x=b),μ.real {x}) ≤
        ∑ x∈S.filter (fun x=>π x=b),if x∈A then μ.real {x} else 0 := by
    rw [sum_measureReal_singleton,singleton_event_sum]
    exact hc b hb hG
  have hp := RawPartitionSuccess.finite_partition S (fun x=>μ.real {x})
    (fun _ _=>measureReal_nonneg) π G A a δ ha
    (by simpa only [htotal] using (show (0:ℝ)<1 by norm_num)) hbad' hs
  rwa [htotal,div_one,singleton_event_sum,real_support_restrict μ S hS] at hp

lemma supported_conditional_bad_bound {α ι : Type*} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (S : Finset α) (hS : ∀ᵐ x ∂μ,x∈S) (π : α→ι) (G : Set ι) (A : Set α)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1)
    (hc : ∀ b∈S.image π,b∈G → μ.real (A∩(S.filter (fun x=>π x=b):Set α))/
      μ.real (S.filter (fun x=>π x=b):Set α)≤ε) :
    μ.real A≤ε+μ.real {x | π x∉G} := by
  classical
  have hs (b : ι) (hb : b∈S.image π) (hG : b∈G) :
      (1-ε)*μ.real (S.filter (fun x=>π x=b):Set α)≤
        μ.real (Aᶜ∩(S.filter (fun x=>π x=b):Set α)) := by
    let T:=S.filter (fun x=>π x=b)
    have hj : μ.real (A∩(T:Set α))+μ.real (Aᶜ∩(T:Set α))=μ.real (T:Set α) := by
      rw [←singleton_event_sum,←singleton_event_sum,←sum_measureReal_singleton,
        ←sum_add_distrib]
      apply sum_congr rfl
      intro x hx
      by_cases ha : x∈A <;> simp [ha]
    have hnum : μ.real (A∩(T:Set α))≤ε*μ.real (T:Set α) := by
      by_cases hz : μ.real (T:Set α)=0
      · have hh : μ.real (A∩(T:Set α))≤0 := by
          simpa only [hz] using (measureReal_mono (μ:=μ)
            (Set.inter_subset_right (s:=A) (t:=(T:Set α))))
        simpa only [hz,mul_zero] using hh
      · have hp : 0<μ.real (T:Set α) := lt_of_le_of_ne measureReal_nonneg (Ne.symm hz)
        exact (div_le_iff₀ hp).mp (hc b hb hG)
    change (1-ε)*μ.real (T:Set α)≤μ.real (Aᶜ∩(T:Set α))
    nlinarith
  have hp := supported_partition_lower μ S hS π G Aᶜ (1-ε) (μ.real {x | π x∉G})
    (by linarith) le_rfl hs
  rw [measureReal_compl MeasurableSet.of_discrete,probReal_univ] at hp
  have hδ : 0≤μ.real {x | π x∉G} := measureReal_nonneg
  nlinarith [mul_nonneg hε hδ]

end RoughFaceShift

end
end

end OAI
