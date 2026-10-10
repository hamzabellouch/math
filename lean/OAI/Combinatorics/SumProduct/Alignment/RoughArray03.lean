import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughArray02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

noncomputable section
end

noncomputable section
namespace RoughArrayCoordinates
open RationalLattice RoughFaceShift RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open scoped BigOperators
variable {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G) [MetricSpace (G⧸Γ)]
 

def badPhysical (m v : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η Nloc : ℝ)
    (d : ℕ) (K : Fin v→ℤ) (P : (Fin (m+v)→ℝ)→G)
    (σ : (G⧸Γ)→(G⧸Γ)) (t : Fin m→ℤ) : Prop :=
  ∃ (lo hi : Fin v→ℝ) (res : Fin v→ℤ) (test : (G⧸Γ)→ℂ),
    (∀ i,c₀*Nloc≤hi i-lo i) ∧ (∀ i,-C₀*Nloc≤lo i ∧ hi i≤C₀*Nloc) ∧
    LipschitzWith B test ∧ (∀ y,‖test y‖≤B) ∧
    η≤‖mean (physicalResidueBox lo hi res d)
      (fun b=>test (σ (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ))
        (fun i=>(affine K (∏ j,t j) b i:ℝ)))))))-
    mean (physicalResidueBox lo hi res d)
      (fun b=>test (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ))
        (fun i=>(affine K (∏ j,t j) b i:ℝ))))))‖
end RoughArrayCoordinates
end
noncomputable section
namespace RoughArrayCoordinates
open RationalLattice RoughFaceShift RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open scoped BigOperators
variable {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G) [MetricSpace (G⧸Γ)]
 

omit [TopologicalSpace G] in
theorem badPhysical_subset {m v : ℕ} (c₀ C₀ Ctail Corigin : ℝ) (B : NNReal)
    (η Nloc Z : ℝ) (d M : ℕ) (K A : Fin v→ℤ) (P : (Fin (m+v)→ℝ)→G)
    (σ : (G⧸Γ)→(G⧸Γ)) (t : Fin m→ℤ)
    (hc₀ : 0≤c₀) (hC₀ : 0≤C₀) (ht : 0<∏ j,t j)
    (hscale : Z≤((∏ j,t j:ℤ):ℝ)*Nloc ∧ ((∏ j,t j:ℤ):ℝ)*Nloc≤Ctail*Z)
    (hdt : IsCoprime (d:ℤ) (∏ j,t j)) (hMt : IsCoprime (M:ℤ) (∏ j,t j))
    (hKdiv : ∀ i,(∏ j,t j)∣(M:ℤ)*K i+A i) (hK : ∀ i,|(K i:ℝ)|≤Corigin*Z) :
    badPhysical Γ m v c₀ C₀ B η Nloc d K P σ t →
      badFace Γ m v c₀ (Corigin+C₀*Ctail) B η Z d M A P σ t
 := by
  rintro ⟨lo,hi,res,test,hside,hbox,hLip,hbound,hbad⟩
  refine ⟨endpoint K (∏ j,t j) lo,endpoint K (∏ j,t j) hi,
    affine K (∏ j,t j) res,test,?_,?_,hLip,hbound,?_⟩
  · intro i
    have htr : (0:ℝ)<((∏ j,t j:ℤ):ℝ) := by exact_mod_cast ht
    have h1:=mul_le_mul_of_nonneg_left (hside i) htr.le
    have h2:=mul_le_mul_of_nonneg_left hscale.1 hc₀
    dsimp [endpoint]
    nlinarith
  · intro i
    have htr : (0:ℝ)<((∏ j,t j:ℤ):ℝ) := by exact_mod_cast ht
    have h1:=mul_le_mul_of_nonneg_left (hbox i).1 htr.le
    have h2:=mul_le_mul_of_nonneg_left (hbox i).2 htr.le
    have h3:=mul_le_mul_of_nonneg_left hscale.2 hC₀
    have h4 : -Corigin*Z≤(K i:ℝ) ∧ (K i:ℝ)≤Corigin*Z := by
      have hh:=(abs_le.mp (hK i))
      constructor <;> nlinarith [hh.1,hh.2]
    dsimp [endpoint]
    constructor <;> nlinarith [h4.1,h4.2]
  · rw [←mean_affine_nested K A res (∏ j,t j) ht d M hdt hMt hKdiv lo hi,
      ←mean_affine_nested K A res (∏ j,t j) ht d M hdt hMt hKdiv lo hi]
    exact hbad

end RoughArrayCoordinates
end

noncomputable section
namespace RoughArrayCoordinates
open RationalLattice RoughFaceShift RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open ProductExposureLabels ProductExposureLaw
open scoped BigOperators

 
def rStar {m : ℕ} (M : ℕ) (b : Label m) : ℤ :=
  ((∏ j,b.residue j)*b.pivotResidue)%(M:ℤ)

 
def yStar {m : ℕ} (M : ℕ) (R : ℝ) (b : Label m) : ℤ := ⌊b.left R/(M:ℝ)⌋

def coarseOrigin {m : ℕ} (a M : ℕ) (R : ℝ) (b : Label m) : Fin (a+1)→ℤ :=
  Pi.single 0 ((M:ℤ)*yStar M R b+rStar M b)

 
def physicalOrigin {m : ℕ} (a M : ℕ) (R : ℝ) (b : Label m)
    (t pstar : ℤ) : Fin (a+1)→ℤ :=
  Pi.single 0 ((t*pstar-rStar M b)/(M:ℤ)-yStar M R b)

 

def rawPhysicalEvent {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G)
    [MetricSpace (G⧸Γ)] (m a : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η R : ℝ)
    (d M : ℕ) (L : ℤ) (F : Label m→FaceData m (a+1) G Γ) :
    Set ((Fin m→ℕ)×ℕ) :=
  {z | let b:=expose L (M:ℤ) R z
       ∃ pstar : ℤ,(M:ℤ)∣pstar-(z.2:ℤ) ∧ |(pstar:ℝ)-(z.2:ℝ)|≤R ∧
         badPhysical Γ m (a+1) c₀ C₀ B η (R/(M:ℝ)) d
           (physicalOrigin a M R b (∏ j,(z.1 j:ℤ)) pstar)
           (F b).P (F b).σ (fun j=>(z.1 j:ℤ))}
end RoughArrayCoordinates
end

noncomputable section
namespace RoughArrayCoordinates
open ProductExposureLabels RoughFaceShift RoughScales
open scoped BigOperators

lemma scalar_origin_bound (M : ℕ) (hM : 0<M) (t p pstar r : ℤ)
    (ht : 0<t) (hr : 0≤r ∧ r<(M:ℤ)) (hdiv : (M:ℤ)∣t*pstar-r)
    (Q R S C Z : ℝ) (hR : 0≤R) (hZ : 1≤Z) (hZM : Z*(M:ℝ)=S*R)
    (htS : (t:ℝ)≤C*S) (hbin : Q≤(t:ℝ)*(p:ℝ) ∧ (t:ℝ)*(p:ℝ)<Q+S*R)
    (hcell : |(pstar:ℝ)-(p:ℝ)|≤R) :
    |(((t*pstar-r)/(M:ℤ)-⌊Q/(M:ℝ)⌋:ℤ):ℝ)|≤(C+2)*Z := by
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have htr : (0:ℝ)<(t:ℝ) := by exact_mod_cast ht
  have hrl : (0:ℝ)≤(r:ℝ) := by exact_mod_cast hr.1
  have hru : (r:ℝ)<(M:ℝ) := by exact_mod_cast hr.2
  let k : ℤ := (t*pstar-r)/(M:ℤ)-⌊Q/(M:ℝ)⌋
  have hk0 : (M:ℤ)*(k+⌊Q/(M:ℝ)⌋)=t*pstar-r := by
    dsimp [k]
    rw [sub_add_cancel,Int.mul_ediv_cancel']
    exact hdiv
  have hk : (M:ℝ)*((k:ℝ)+(⌊Q/(M:ℝ)⌋:ℝ))=(t:ℝ)*(pstar:ℝ)-(r:ℝ) := by
    exact_mod_cast hk0
  have hfl := Int.floor_le (Q/(M:ℝ))
  have hfu := Int.lt_floor_add_one (Q/(M:ℝ))
  have hfl' : (⌊Q/(M:ℝ)⌋:ℝ)*(M:ℝ)≤Q := (le_div_iff₀ hMr).mp hfl
  have hfu' : Q<((⌊Q/(M:ℝ)⌋:ℝ)+1)*(M:ℝ) := (div_lt_iff₀ hMr).mp hfu
  have hcell' := abs_le.mp hcell
  have hcl := mul_le_mul_of_nonneg_left hcell'.1 htr.le
  have hcu := mul_le_mul_of_nonneg_left hcell'.2 htr.le
  have htR := mul_le_mul_of_nonneg_right htS hR
  have hZR := mul_le_mul_of_nonneg_right hZ hMr.le
  change |(k:ℝ)|≤(C+2)*Z
  apply abs_le.mpr
  have hCZM:=congrArg (fun x : ℝ=>C*x) hZM
  constructor
  · apply (mul_le_mul_iff_left₀ hMr).mp
    nlinarith [hbin.1,hbin.2]
  · apply (mul_le_mul_iff_left₀ hMr).mp
    nlinarith [hbin.1,hbin.2]

lemma rStar_expose {m : ℕ} (M : ℕ) (L : ℤ) (hML : (M:ℤ)∣L)
    (R : ℝ) (z : (Fin m→ℕ)×ℕ) :
    rStar M (expose L (M:ℤ) R z)=((∏ j,(z.1 j:ℤ))*(z.2:ℤ))%(M:ℤ) := by
  unfold rStar expose
  have hmod (j : Fin m) : ((z.1 j:ℤ)%L)%(M:ℤ)=(z.1 j:ℤ)%(M:ℤ) :=
    Int.emod_emod_of_dvd _ hML
  rw [Int.mul_emod,Int.emod_emod,Finset.prod_int_mod]
  simp only [hmod]
  rw [←Finset.prod_int_mod,←Int.mul_emod]

lemma physicalOrigin_div {m : ℕ} (a M : ℕ) (L : ℤ) (hML : (M:ℤ)∣L)
    (R : ℝ) (z : (Fin m→ℕ)×ℕ) (pstar : ℤ) (hp : (M:ℤ)∣pstar-(z.2:ℤ)) :
    ∀ i,(∏ j,(z.1 j:ℤ))∣(M:ℤ)*
      physicalOrigin a M R (expose L (M:ℤ) R z) (∏ j,(z.1 j:ℤ)) pstar i+
      coarseOrigin a M R (expose L (M:ℤ) R z) i := by
  let b:=expose L (M:ℤ) R z
  let t:ℤ:=∏ j,(z.1 j:ℤ)
  have hr : rStar M b=(t*(z.2:ℤ))%(M:ℤ) := rStar_expose M L hML R z
  have hdiv : (M:ℤ)∣t*pstar-rStar M b := by
    rw [hr]
    have h1 : (M:ℤ)∣t*(pstar-(z.2:ℤ)) := dvd_mul_of_dvd_right hp t
    have h2 : (M:ℤ)∣t*(z.2:ℤ)-(t*(z.2:ℤ))%(M:ℤ) := by
      rw [Int.dvd_iff_emod_eq_zero,Int.sub_emod,Int.emod_emod]
      simp
    have he : t*pstar-(t*(z.2:ℤ))%(M:ℤ)=
        t*(pstar-(z.2:ℤ))+(t*(z.2:ℤ)-(t*(z.2:ℤ))%(M:ℤ)) := by ring
    rw [he]
    exact dvd_add h1 h2
  intro i
  change t∣(M:ℤ)*(Pi.single 0 ((t*pstar-rStar M b)/(M:ℤ)-yStar M R b) : Fin (a+1)→ℤ) i+
    (Pi.single 0 ((M:ℤ)*yStar M R b+rStar M b) : Fin (a+1)→ℤ) i
  by_cases hi:i=0
  · subst i
    simp only [Pi.single_eq_same]
    have hh : (M:ℤ)*((t*pstar-rStar M b)/(M:ℤ))=t*pstar-rStar M b :=
      Int.mul_ediv_cancel' hdiv
    have he : (M:ℤ)*((t*pstar-rStar M b)/(M:ℤ)-yStar M R b)+
        ((M:ℤ)*yStar M R b+rStar M b)=t*pstar := by linear_combination hh
    rw [he]
    exact dvd_mul_right t pstar
  · simp [Pi.single_eq_of_ne hi]

end RoughArrayCoordinates
end

noncomputable section
namespace RoughArrayCoordinates
open RationalLattice RoughFaceShift RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open ProductExposureLabels ProductExposureLaw RoughScales RawHarmonicProbability
open scoped BigOperators

lemma physicalOrigin_bound {m : ℕ} (a M : ℕ) (hM : 0<M) (L : ℤ) (hML : (M:ℤ)∣L)
    (R : ℝ) (hR : 0<R) (hRM : 1≤R/(M:ℝ))
    (z : (Fin m→ℕ)×ℕ) (ht : ∀ j,0<z.1 j) (pstar : ℤ)
    (hp : (M:ℤ)∣pstar-(z.2:ℤ)) (hcell : |(pstar:ℝ)-(z.2:ℝ)|≤R) :
    ∀ i,|(physicalOrigin a M R (expose L (M:ℤ) R z) (∏ j,(z.1 j:ℤ)) pstar i:ℝ)|≤
      ((2:ℝ)^m+2)*(labelExposure (expose L (M:ℤ) R z) R M).Z := by
  let b:=expose L (M:ℤ) R z
  let t:ℤ:=∏ j,(z.1 j:ℤ)
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have htpos : 0<t := Finset.prod_pos (fun j _=>by exact_mod_cast ht j)
  have htcast : (t:ℝ)=∏ j,(z.1 j:ℝ) := by simp [t]
  have hr : 0≤rStar M b ∧ rStar M b<(M:ℤ) := by
    exact ⟨Int.emod_nonneg _ (by exact_mod_cast (Nat.ne_of_gt hM)),
      Int.emod_lt_of_pos _ (by exact_mod_cast hM)⟩
  have hs1 : (1:ℝ)≤∏ j,b.scales j :=
    Finset.one_le_prod₀ (fun j _=>one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have hZ1 : 1≤(labelExposure b R M).Z := by
    change 1≤((∏ j,b.scales j)*R)/(M:ℝ)
    have hh:=mul_le_mul_of_nonneg_right hs1 (div_nonneg hR.le hMr.le)
    rw [mul_div_assoc]
    linarith
  have hZM : (labelExposure b R M).Z*(M:ℝ)=(∏ j,b.scales j)*R := by
    dsimp [labelExposure,Label.width]
    exact div_mul_cancel₀ _ hMr.ne'
  obtain ⟨hdy,hbin⟩:=expose_bounds L (M:ℤ) R hR z ht
  have hbd:=product_dyadic_bounds b z.1 hdy
  have hdiv : (M:ℤ)∣t*pstar-rStar M b := by
    rw [rStar_expose M L hML R z]
    have h1 : (M:ℤ)∣t*(pstar-(z.2:ℤ)) := dvd_mul_of_dvd_right hp t
    have h2 : (M:ℤ)∣t*(z.2:ℤ)-(t*(z.2:ℤ))%(M:ℤ) := by
      rw [Int.dvd_iff_emod_eq_zero,Int.sub_emod,Int.emod_emod];simp
    have he : t*pstar-(t*(z.2:ℤ))%(M:ℤ)=
        t*(pstar-(z.2:ℤ))+(t*(z.2:ℤ)-(t*(z.2:ℤ))%(M:ℤ)) := by ring
    rw [he]
    exact dvd_add h1 h2
  have hbound:=scalar_origin_bound M hM t (z.2:ℤ) pstar (rStar M b) htpos hr hdiv
    (b.left R) R (∏ j,b.scales j) ((2:ℝ)^m) (labelExposure b R M).Z hR.le hZ1 hZM
    (by simpa only [htcast] using hbd.2) (by simpa only [htcast,Int.cast_natCast,Label.width] using hbin) hcell
  intro i
  change |((Pi.single 0 ((t*pstar-rStar M b)/(M:ℤ)-yStar M R b) : Fin (a+1)→ℤ) i:ℝ)|≤_
  by_cases hi:i=0
  · subst i
    simpa only [Pi.single_eq_same,yStar] using hbound
  · simp only [Pi.single_eq_of_ne hi,Int.cast_zero,abs_zero]
    positivity

 

lemma rawPhysical_subset {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G)
    [MetricSpace (G⧸Γ)] (m a w M d : ℕ) (hd : 0<d) (hdw : d≤w)
    (X : Fin m→ℕ) (Xp : ℕ) (hX : ∀ j,0<X j) (hM : 0<M) (hMs : Smooth w (M:ℤ))
    (R : ℝ) (hR : 0<R) (hRM : 1≤R/(M:ℝ)) (L : ℤ) (hML : (M:ℤ)∣L)
    (c₀ C₀ : ℝ) (hc₀ : 0≤c₀) (hC₀ : 0≤C₀) (B : NNReal) (η : ℝ)
    (F : Label m→FaceData m (a+1) G Γ)
    (hF : ∀ b,(F b).A=coarseOrigin a M R b) :
    rawPhysicalEvent Γ m a c₀ C₀ B η R d M L F ∩
      (fullDomain X Xp (primorial w):Set _) ⊆
      rawFaceEvent Γ m (a+1) c₀ ((2:ℝ)^m+2+C₀*2^m) B η R d M L F := by
  rintro z ⟨hz,hdom⟩
  obtain ⟨pstar,hp,hcell,hbad⟩:=hz
  have hdom' : ∀ j,z.1 j∈units (X j) (primorial w) := by
    have HH:=(Finset.mem_filter.mp hdom).1
    exact Fintype.mem_piFinset.mp (Finset.mem_product.mp HH).1
  have ht : ∀ j,0<z.1 j := fun j=>(hX j).trans_le (Finset.mem_Ico.mp
    (Finset.mem_filter.mp (hdom' j)).1).1
  have hcop : ∀ j,(primorial w).Coprime (z.1 j) := fun j=>(Finset.mem_filter.mp (hdom' j)).2
  have hrough : ∀ j,Rough w (z.1 j:ℤ) := fun j=>
    (rough_iff_coprime w _).mpr (by simpa only [Int.natAbs_natCast] using (hcop j).symm)
  have hdt : IsCoprime (d:ℤ) (∏ j,(z.1 j:ℤ)) := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    have HH:=Nat.Coprime.prod_right (fun j (_ : j∈Finset.univ)=>period_coprime_of_rough w d (z.1 j) hd hdw (hcop j).symm)
    simpa only [←Nat.cast_prod,Int.natAbs_natCast] using HH
  have hMt : IsCoprime (M:ℤ) (∏ j,(z.1 j:ℤ)) := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    have HH:=Nat.Coprime.prod_right (fun j (_ : j∈Finset.univ)=>smooth_nat_coprime_rough hMs (hrough j))
    simpa only [←Nat.cast_prod,Int.natAbs_natCast] using HH
  let b:=expose L (M:ℤ) R z
  let Z:ℝ:=(labelExposure b R M).Z
  have hs:=product_dyadic_bounds b z.1 (expose_bounds L (M:ℤ) R hR z ht).1
  have hscale : Z≤((∏ j,(z.1 j:ℤ):ℤ):ℝ)*(R/(M:ℝ)) ∧
      ((∏ j,(z.1 j:ℤ):ℤ):ℝ)*(R/(M:ℝ))≤(2:ℝ)^m*Z := by
    have hRdiv : 0≤R/(M:ℝ) := div_nonneg hR.le (by positivity)
    constructor
    · simpa [Z,labelExposure,Label.width,mul_div_assoc] using mul_le_mul_of_nonneg_right hs.1 hRdiv
    · simpa [Z,labelExposure,Label.width,mul_div_assoc,mul_assoc] using mul_le_mul_of_nonneg_right hs.2 hRdiv
  change badFace Γ m (a+1) c₀ ((2:ℝ)^m+2+C₀*2^m) B η Z d M (F b).A (F b).P (F b).σ _
  rw [hF b]
  exact badPhysical_subset Γ c₀ C₀ ((2:ℝ)^m) ((2:ℝ)^m+2) B η (R/(M:ℝ)) Z d M
    (physicalOrigin a M R b (∏ j,(z.1 j:ℤ)) pstar) (coarseOrigin a M R b) (F b).P (F b).σ
    (fun j=>(z.1 j:ℤ)) hc₀ hC₀ (Finset.prod_pos (fun j _=>by exact_mod_cast ht j)) hscale hdt hMt
    (physicalOrigin_div a M L hML R z pstar hp) (physicalOrigin_bound a M hM L hML R hR hRM z ht pstar hp hcell) hbad

end RoughArrayCoordinates

end

end OAI
