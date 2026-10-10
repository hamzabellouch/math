import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.ProductExposure02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
noncomputable section
end
end

section
noncomputable section
namespace ProductExposureCutoff
open RawHarmonicProbability Finset Filter MeasureTheory
open scoped Topology BigOperators

def badBin (X : ℕ) (R : ℝ) (m : ℕ) (tlo τ : ℝ) : Set ℕ := {p | ∃ Q : ℝ,
  Q≤τ*p ∧ τ*p<Q+tlo*R ∧ ∃ τ' : ℝ, tlo≤τ' ∧ τ'≤2^m*tlo ∧
    (Q/τ'<X+2*R ∨ (X:ℝ)^2-2*R<(Q+tlo*R)/τ')}

lemma bad_bin_geometry (X R B tlo τ τ' Q p : ℝ)
    (hX : 4≤X) (hRX : R≤X) (hR : 0≤R) (hB : 1≤B) (htlo : 0<tlo)
    (ht : tlo≤τ) (ht' : τ≤B*tlo) (hu : tlo≤τ') (hu' : τ'≤B*tlo)
    (hp : X≤p) (hQ : Q≤τ*p) (hQ' : τ*p<Q+tlo*R)
    (hbad : Q/τ'<X+2*R ∨ X^2-2*R<(Q+tlo*R)/τ') :
    p≤4*B*X ∨ X^2≤4*B*p := by
  have hp0 : 0≤p := by linarith
  have hu0 : 0<τ' := htlo.trans_le hu
  have hB0 : 0≤B := by linarith
  have hX0 : 0≤X := by linarith
  have hUX : 0≤X+2*R := by positivity
  have hVX : 0≤X^2-2*R := by nlinarith
  rcases hbad with hbad | hbad
  · left
    have hbad' := (div_lt_iff₀ hu0).mp hbad
    have hmu := mul_le_mul_of_nonneg_right hu' hUX
    have hmt := mul_le_mul_of_nonneg_right ht hp0
    have hbr := mul_le_mul_of_nonneg_left hRX hB0
    have hbx := mul_le_mul_of_nonneg_right hB hX0
    have hsmall : p<B*(X+2*R)+R := by
      apply (mul_lt_mul_iff_left₀ htlo).mp
      nlinarith
    nlinarith
  · right
    have hbad' := (lt_div_iff₀ hu0).mp hbad
    have hmu := mul_le_mul_of_nonneg_right hu hVX
    have hmt := mul_le_mul_of_nonneg_right ht' hp0
    have hlarge : X^2-3*R<B*p := by
      apply (mul_lt_mul_iff_left₀ htlo).mp
      nlinarith
    nlinarith

lemma bad_bin_subset_cutoff (X : ℕ) (R : ℝ) (m : ℕ) (tlo τ : ℝ)
    (hX : 4≤X) (hR : 0≤R) (hRX : R≤X) (htlo : 0<tlo)
    (ht : tlo≤τ) (ht' : τ≤2^m*tlo) :
    badBin X R m tlo τ ∩ {p | X≤p} ⊆ cutoff X (m+2) := by
  rintro p ⟨⟨Q,hQ,hQ',τ',hu,hu',hbad⟩,hp⟩
  have hh := bad_bin_geometry (X:ℝ) R (2^m) tlo τ τ' Q p (by exact_mod_cast hX)
    hRX hR (one_le_pow₀ (by norm_num)) htlo ht ht' hu hu' (by exact_mod_cast hp) hQ hQ' hbad
  have he : (2:ℝ)^(m+2)=4*2^m := by rw [pow_add]; norm_num; ring
  change p≤2^(m+2)*X ∨ X^2≤2^(m+2)*p
  rw [←he] at hh
  exact_mod_cast hh

lemma raw_bad_bin_le_cutoff (X W : ℕ) (m : ℕ)
    (hW : 0<W) (hX : 4*W≤X) (R tlo τ : ℝ) (hR : 0≤R) (hRX : R≤X)
    (htlo : 0<tlo) (ht : tlo≤τ) (ht' : τ≤2^m*tlo) :
    (law X W hW hX : Measure ℕ).real (badBin X R m tlo τ) ≤
      (law X W hW hX : Measure ℕ).real (cutoff X (m+2)) := by
  classical
  rw [law_apply,law_apply]
  apply div_le_div_of_nonneg_right _ (mass_pos X W hW hX).le
  apply sum_le_sum
  intro p hp
  obtain ⟨hxp,hpx⟩ := mem_Ico.mp hp
  have hs := bad_bin_subset_cutoff X R m tlo τ (by omega) hR hRX htlo ht ht'
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact False.elim (h₂ ⟨h₁.1,hs ⟨h₁.2,hxp⟩⟩)
  · positivity
  · rfl

theorem raw_bad_bin_decay (X W : ℕ→ℕ) (m : ℕ)
    (hW : ∀ n,0<W n) (hX : ∀ n,4*W n≤X n) (hXt : Tendsto X atTop atTop) :
    ∀ ε : ℝ,0<ε → ∀ᶠ n in atTop,
      ∀ (R tlo τ : ℝ), 0≤R → R≤X n → 0<tlo → tlo≤τ → τ≤2^m*tlo →
        (law (X n) (W n) (hW n) (hX n) : Measure ℕ).real
          (badBin (X n) R m tlo τ)<ε := by
  intro ε hε
  have hh := (raw_cutoff_decay X W (m+2) hW hX hXt).eventually_lt_const hε
  filter_upwards [hh] with n hn
  intro R tlo τ hR hRX htlo ht ht'
  exact (raw_bad_bin_le_cutoff (X n) (W n) m (hW n) (hX n) R tlo τ
    hR hRX htlo ht ht').trans_lt hn

end ProductExposureCutoff
end
end

section
noncomputable section
namespace ProductExposureLabels
open scoped BigOperators Topology
open MeasureTheory Filter RawHarmonicProbability ProductExposureLaw ProductExposureCutoff
attribute [local instance] Classical.propDecidable

def Good {m : ℕ} (X : Fin m→ℕ) (Xp : ℕ) (R : ℝ) (b : Label m) : Prop :=
  (∀ j,(X j:ℝ)≤b.scales j ∧ 2*b.scales j≤(X j:ℝ)^2) ∧
  ∀ τ : ℝ,(∏ j,b.scales j)≤τ →τ≤2^m*(∏ j,b.scales j) →
    Xp+2*R≤b.left R/τ ∧ (b.left R+b.width R)/τ≤(Xp:ℝ)^2-2*R

lemma tail_marginal {m : ℕ} (X : Fin m→ℕ) (Xp W : ℕ) (hW : 0<W)
    (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp) (j : Fin m) (A : Set ℕ) :
    (jointLaw X Xp W hW hX hXp).real {z | z.1 j∈A} =
      (law (X j) W hW (hX j):Measure ℕ).real A := by
  have hf : MeasurePreserving (fun z : (Fin m→ℕ)×ℕ=>z.1 j)
      (jointLaw X Xp W hW hX hXp) (law (X j) W hW (hX j):Measure ℕ) :=
    (measurePreserving_eval (fun i=>(law (X i) W hW (hX i):Measure ℕ)) j).comp
      measurePreserving_fst
  exact hf.measureReal_preimage MeasurableSet.of_discrete.nullMeasurableSet

lemma pivot_marginal {m : ℕ} (X : Fin m→ℕ) (Xp W : ℕ) (hW : 0<W)
    (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp) (A : Set ℕ) :
    (jointLaw X Xp W hW hX hXp).real {z | z.2∈A} =
      (law Xp W hW hXp:Measure ℕ).real A := by
  exact (measurePreserving_snd (μ:=Measure.pi (fun j=>(law (X j) W hW (hX j):Measure ℕ)))
    (ν:=(law Xp W hW hXp:Measure ℕ))).measureReal_preimage
      MeasurableSet.of_discrete.nullMeasurableSet

lemma law_ae_units (X W : ℕ) (hW : 0<W) (hX : 4*W≤X) :
    ∀ᵐ t ∂(law X W hW hX:Measure ℕ),t∈units X W := by
  rw [ae_iff,←measureReal_eq_zero_iff]
  have hh := MicrocellSaturation.law_restrict_units X W hW hX ((units X W:Set ℕ)ᶜ)
  change (law X W hW hX:Measure ℕ).real ((units X W:Set ℕ)ᶜ)=0
  simpa only [Set.compl_inter_self,measureReal_empty] using hh.symm

lemma joint_ae_domain {m : ℕ} (X : Fin m→ℕ) (Xp W : ℕ) (hW : 0<W)
    (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp) :
    ∀ᵐ z ∂jointLaw X Xp W hW hX hXp,z∈rawDomain X Xp W := by
  have ht : ∀ j,∀ᵐ z ∂jointLaw X Xp W hW hX hXp,z.1 j∈units (X j) W := by
    intro j
    rw [ae_iff,←measureReal_eq_zero_iff]
    change (jointLaw X Xp W hW hX hXp).real {z | z.1 j∈(units (X j) W:Set ℕ)ᶜ}=0
    rw [tail_marginal]
    exact (measureReal_eq_zero_iff (by finiteness)).mpr (ae_iff.mp (law_ae_units (X j) W hW (hX j)))
  have hp : ∀ᵐ z ∂jointLaw X Xp W hW hX hXp,z.2∈units Xp W := by
    rw [ae_iff,←measureReal_eq_zero_iff]
    change (jointLaw X Xp W hW hX hXp).real {z | z.2∈(units Xp W:Set ℕ)ᶜ}=0
    rw [pivot_marginal]
    exact (measureReal_eq_zero_iff (by finiteness)).mpr (ae_iff.mp (law_ae_units Xp W hW hXp))
  filter_upwards [ae_all_iff.mpr ht,hp] with z hz hp
  simpa only [rawDomain,Finset.product_eq_sprod,Finset.mem_product,Fintype.mem_piFinset] using
    And.intro hz (Finset.mem_filter.mp hp).1

lemma joint_restrict_domain {m : ℕ} (X : Fin m→ℕ) (Xp W : ℕ) (hW : 0<W)
    (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp) (A : Set ((Fin m→ℕ)×ℕ)) :
    (jointLaw X Xp W hW hX hXp).real (A∩(rawDomain X Xp W:Set _)) =
      (jointLaw X Xp W hW hX hXp).real A := by
  apply measureReal_congr
  filter_upwards [joint_ae_domain X Xp W hW hX hXp] with z hz
  change (z∈A ∧ z∈rawDomain X Xp W) = (z∈A)
  exact propext ⟨And.left,fun ha=>⟨ha,hz⟩⟩

lemma expose_bounds {m : ℕ} (L M : ℤ) (R : ℝ) (hR : 0<R)
    (z : (Fin m→ℕ)×ℕ) (ht : ∀ j,0<z.1 j) :
    (∀ j,(expose L M R z).scales j≤(z.1 j:ℝ) ∧
      (z.1 j:ℝ)<2*(expose L M R z).scales j) ∧
    (expose L M R z).left R≤(∏ j,(z.1 j:ℝ))*(z.2:ℝ) ∧
    (∏ j,(z.1 j:ℝ))*(z.2:ℝ)<(expose L M R z).left R+(expose L M R z).width R := by
  refine ⟨fun j=>(dyadic_iff _ _ (ht j)).mp rfl,?_⟩
  exact (floor_bin_iff _ _ _ ((expose L M R z).width_pos R hR)).mp rfl

lemma product_dyadic_bounds {m : ℕ} (b : Label m) (t : Fin m→ℕ)
    (ht : ∀ j,b.scales j≤(t j:ℝ) ∧ (t j:ℝ)<2*b.scales j) :
    (∏ j,b.scales j)≤(∏ j,(t j:ℝ)) ∧
    (∏ j,(t j:ℝ))≤2^m*(∏ j,b.scales j) := by
  constructor
  · exact Finset.prod_le_prod₀ (fun j _=>by unfold Label.scales; positivity) (fun j _=>(ht j).1)
  · calc
      _ ≤ ∏ j,2*b.scales j := Finset.prod_le_prod₀ (fun _ _=>by positivity) (fun j _=>(ht j).2.le)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp

lemma good_of_not_cutoff {m : ℕ} (X : Fin m→ℕ) (Xp W : ℕ)
    (hX : ∀ j,0<X j) (hXp : 4≤Xp) (L M : ℤ) (R : ℝ) (hR : 0<R) (hRX : R≤Xp)
    (z : (Fin m→ℕ)×ℕ) (hz : z∈rawDomain X Xp W)
    (htc : ∀ j,z.1 j∉cutoff (X j) 1) (hpc : z.2∉cutoff Xp (m+2)) :
    Good X Xp R (expose L M R z) := by
  obtain ⟨hzT,hzP⟩ : (∀ j,z.1 j∈units (X j) W) ∧ z.2∈Finset.Ico Xp (Xp^2) := by
    simpa [rawDomain,Finset.product_eq_sprod] using hz
  have htpos : ∀ j,0<z.1 j := fun j=>(hX j).trans_le (Finset.mem_Ico.mp
    (Finset.mem_filter.mp (hzT j)).1).1
  obtain ⟨hdy,hq,hq'⟩ := expose_bounds L M R hR z htpos
  obtain ⟨hprod,hprod'⟩ := product_dyadic_bounds (expose L M R z) z.1 hdy
  have hspos : 0<∏ j,(expose L M R z).scales j :=
    Finset.prod_pos (fun j _=>pow_pos (by norm_num) _)
  constructor
  · intro j
    have hcut : ¬(z.1 j≤2*X j ∨(X j)^2≤2*z.1 j) := by
      simpa [cutoff] using htc j
    push Not at hcut
    have hl : (2:ℝ)*X j<(z.1 j:ℝ) := by exact_mod_cast hcut.1
    have hu : (2:ℝ)*(z.1 j:ℝ)<(X j:ℝ)^2 := by exact_mod_cast hcut.2
    constructor <;> nlinarith [(hdy j).1,(hdy j).2]
  · intro τ hτ hτ'
    by_contra hn
    have hbad : (expose L M R z).left R/τ<Xp+2*R ∨
        (Xp:ℝ)^2-2*R<((expose L M R z).left R+(expose L M R z).width R)/τ := by
      rcases not_and_or.mp hn with hn | hn
      · exact Or.inl (lt_of_not_ge hn)
      · exact Or.inr (lt_of_not_ge hn)
    have hh := bad_bin_geometry (Xp:ℝ) R (2^m) (∏ j,(expose L M R z).scales j)
      (∏ j,(z.1 j:ℝ)) τ ((expose L M R z).left R) z.2
      (by exact_mod_cast hXp) hRX hR.le (one_le_pow₀ (by norm_num)) hspos
      hprod hprod' hτ hτ' (by exact_mod_cast (Finset.mem_Ico.mp hzP).1) hq hq' hbad
    have he : (2:ℝ)^(m+2)=4*2^m := by rw [pow_add]; norm_num; ring
    apply hpc
    change z.2≤2^(m+2)*Xp ∨ Xp^2≤2^(m+2)*z.2
    rw [←he] at hh
    exact_mod_cast hh

lemma bad_good_bound {m : ℕ} (X : Fin m→ℕ) (Xp W : ℕ) (hW : 0<W)
    (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp) (L M : ℤ) (R : ℝ) (hR : 0<R) (hRX : R≤Xp) :
    (jointLaw X Xp W hW hX hXp).real {z | ¬Good X Xp R (expose L M R z)} ≤
      (∑ j,(law (X j) W hW (hX j):Measure ℕ).real (cutoff (X j) 1)) +
        (law Xp W hW hXp:Measure ℕ).real (cutoff Xp (m+2)) := by
  rw [←joint_restrict_domain]
  have hsub : {z | ¬Good X Xp R (expose L M R z)}∩(rawDomain X Xp W:Set _) ⊆
      (⋃ j,{z | z.1 j∈cutoff (X j) 1})∪{z | z.2∈cutoff Xp (m+2)} := by
    intro z hz
    by_contra hn
    have hp : z.2∉cutoff Xp (m+2) := fun h=>hn (Or.inr h)
    have ht : ∀ j,z.1 j∉cutoff (X j) 1 := fun j h=>hn (Or.inl (Set.mem_iUnion.mpr ⟨j,h⟩))
    exact hz.1 (good_of_not_cutoff X Xp W (fun j=>by have:=hX j; omega)
      (by omega) L M R hR hRX z hz.2 ht hp)
  calc
    _ ≤ _ := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ (∑ j,(jointLaw X Xp W hW hX hXp).real {z | z.1 j∈cutoff (X j) 1})+
        (jointLaw X Xp W hW hX hXp).real {z | z.2∈cutoff Xp (m+2)} :=
      add_le_add (measureReal_iUnion_fintype_le _) le_rfl
    _ = _ := by simp only [tail_marginal,pivot_marginal]

 

theorem raw_good_decay {m : ℕ} (X : ℕ→Fin m→ℕ) (Xp W : ℕ→ℕ)
    (L M : ℕ→ℤ) (R : ℕ→ℝ) (hW : ∀ n,0<W n)
    (hX : ∀ n j,4*W n≤X n j) (hXp : ∀ n,4*W n≤Xp n)
    (hXt : ∀ j,Tendsto (fun n=>X n j) atTop atTop)
    (hXpt : Tendsto Xp atTop atTop) (hR : ∀ n,0<R n) (hRX : ∀ n,R n≤Xp n) :
    Tendsto (fun n=>(jointLaw (X n) (Xp n) (W n) (hW n) (hX n) (hXp n)).real
      {z | ¬Good (X n) (Xp n) (R n) (expose (L n) (M n) (R n) z)}) atTop (𝓝 0)
 := by
  apply squeeze_zero (fun _=>measureReal_nonneg) (fun n=>
    bad_good_bound (X n) (Xp n) (W n) (hW n) (hX n) (hXp n) (L n) (M n) (R n) (hR n) (hRX n))
  have htail := tendsto_finsetSum Finset.univ (fun j _=>
    raw_cutoff_decay (fun n=>X n j) W 1 hW (fun n=>hX n j) (hXt j))
  have hp := raw_cutoff_decay Xp W (m+2) hW hXp hXpt
  simpa using htail.add hp

end ProductExposureLabels

end
end

end OAI
