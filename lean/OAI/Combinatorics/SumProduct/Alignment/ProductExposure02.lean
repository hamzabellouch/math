import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.ProductExposure01
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

 
theorem source_raw_joint_face_uniform (hsk : SecondKind c)
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
  have hu := raw_conditional_face_uniform (Γ:=Γ) (c:=c) hsk hΓ htop m v D d hd
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

end RoughFaceShift
end
end

section
noncomputable section
namespace ProductExposureLabels
open scoped BigOperators
open HarmonicExposure ProductExposureLaw
attribute [local instance] Classical.propDecidable

structure Label (m : ℕ) where
  dyadic : Fin m → ℕ
  residue : Fin m → ℤ
  pivotResidue : ℤ
  bin : ℤ

def Label.scales {m : ℕ} (b : Label m) (j : Fin m) : ℝ := 2 ^ b.dyadic j

def Label.width {m : ℕ} (b : Label m) (R : ℝ) : ℝ := (∏ j,b.scales j)*R

def Label.left {m : ℕ} (b : Label m) (R : ℝ) : ℝ := b.bin*b.width R

def expose {m : ℕ} (L M : ℤ) (R : ℝ) (z : (Fin m→ℕ)×ℕ) : Label m where
  dyadic := fun j=>(z.1 j).log2
  residue := fun j=>(z.1 j:ℤ)%L
  pivotResidue := (z.2:ℤ)%M
  bin := ⌊(∏ j,(z.1 j:ℝ))*(z.2:ℝ) / ((∏ j,(2:ℝ)^(z.1 j).log2)*R)⌋

def rawDomain {m : ℕ} (X : Fin m→ℕ) (Xp W : ℕ) : Finset ((Fin m→ℕ)×ℕ) :=
  (Fintype.piFinset (fun j=>RawHarmonicProbability.units (X j) W)).product
    (Finset.Ico Xp (Xp^2))

@[ext] lemma Label.ext {m : ℕ} {a b : Label m} (h₁ : a.dyadic=b.dyadic)
    (h₂ : a.residue=b.residue) (h₃ : a.pivotResidue=b.pivotResidue)
    (h₄ : a.bin=b.bin) : a=b := by cases a; cases b; simp_all

lemma dyadic_iff (t k : ℕ) (ht : 0<t) :
    t.log2=k ↔ (2:ℝ)^k≤(t:ℝ) ∧ (t:ℝ)<2*(2:ℝ)^k := by
  rw [Nat.log2_eq_iff (by omega)]
  constructor <;> intro h
  · constructor
    · exact_mod_cast h.1
    · have hh : (t:ℝ)<(2:ℝ)^(k+1) := by exact_mod_cast h.2
      simpa [pow_succ,mul_comm] using hh
  · constructor
    · exact_mod_cast h.1
    · have hh : (t:ℝ)<(2:ℝ)^(k+1) := by simpa [pow_succ,mul_comm] using h.2
      exact_mod_cast hh

lemma residue_iff (t L r : ℤ) (hr : 0≤r ∧ r<L) :
    t%L=r ↔ L∣t-r := by
  rw [Int.dvd_iff_emod_eq_zero, ←Int.emod_eq_emod_iff_emod_sub_eq_zero,
    Int.emod_eq_of_lt hr.1 hr.2]

lemma floor_bin_iff (x Δ : ℝ) (k : ℤ) (hΔ : 0<Δ) :
    ⌊x/Δ⌋=k ↔ (k:ℝ)*Δ≤x ∧ x<(k:ℝ)*Δ+Δ := by
  rw [Int.floor_eq_iff,le_div_iff₀ hΔ,div_lt_iff₀ hΔ]
  ring_nf

lemma Label.width_pos {m : ℕ} (b : Label m) (R : ℝ) (hR : 0<R) :
    0<b.width R := by
  unfold Label.width Label.scales
  exact mul_pos (Finset.prod_pos (fun _ _=>pow_pos (by norm_num) _)) hR

lemma expose_eq_iff {m : ℕ} (L M : ℤ) (R : ℝ) (hR : 0<R)
    (z : (Fin m→ℕ)×ℕ) (ht : ∀ j,0<z.1 j) (b : Label m)
    (hr : ∀ j,0≤b.residue j ∧ b.residue j<L)
    (ha : 0≤b.pivotResidue ∧ b.pivotResidue<M) :
    expose L M R z=b ↔
      (∀ j,b.scales j≤(z.1 j:ℝ) ∧ (z.1 j:ℝ)<2*b.scales j) ∧
      (∀ j,L∣(z.1 j:ℤ)-b.residue j) ∧ M∣(z.2:ℤ)-b.pivotResidue ∧
      b.left R≤(∏ j,(z.1 j:ℝ))*(z.2:ℝ) ∧
      (∏ j,(z.1 j:ℝ))*(z.2:ℝ)<b.left R+b.width R := by
  have hw (hd : (fun j=>(z.1 j).log2)=b.dyadic) :
      ((∏ j,(2:ℝ)^(z.1 j).log2)*R)=b.width R := by
    unfold Label.width Label.scales
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [congrFun hd j]
  constructor
  · intro heq
    have hd : (fun j=>(z.1 j).log2)=b.dyadic := congrArg Label.dyadic heq
    have hre : (fun j=>(z.1 j:ℤ)%L)=b.residue := congrArg Label.residue heq
    have hap : (z.2:ℤ)%M=b.pivotResidue := congrArg Label.pivotResidue heq
    have hb : ⌊(∏ j,(z.1 j:ℝ))*(z.2:ℝ)/((∏ j,(2:ℝ)^(z.1 j).log2)*R)⌋=b.bin :=
      congrArg Label.bin heq
    rw [hw hd] at hb
    exact ⟨fun j=>(dyadic_iff _ _ (ht j)).mp (congrFun hd j),
      fun j=>(residue_iff _ _ _ (hr j)).mp (congrFun hre j),
      (residue_iff _ _ _ ha).mp hap,
      (floor_bin_iff _ _ _ (b.width_pos R hR)).mp hb⟩
  · rintro ⟨hd,hrd,had,hb⟩
    have hde : (fun j=>(z.1 j).log2)=b.dyadic :=
      funext (fun j=>(dyadic_iff _ _ (ht j)).mpr (hd j))
    apply Label.ext hde
    · exact funext (fun j=>(residue_iff _ _ _ (hr j)).mpr (hrd j))
    · exact (residue_iff _ _ _ ha).mpr had
    · change ⌊(∏ j,(z.1 j:ℝ))*(z.2:ℝ)/((∏ j,(2:ℝ)^(z.1 j).log2)*R)⌋=b.bin
      rw [hw hde]
      exact (floor_bin_iff _ _ _ (b.width_pos R hR)).mpr hb

 

theorem fiber_eq {m : ℕ} (X : Fin m→ℕ) (Xp W : ℕ) (hX : ∀ j,0<X j)
    (L M : ℤ) (R : ℝ) (_ : 0<L) (_ : 0<M) (hR : 0<R)
    (b : Label m) (hr : ∀ j,0≤b.residue j ∧ b.residue j<L)
    (ha : 0≤b.pivotResidue ∧ b.pivotResidue<M) :
    (rawDomain X Xp W).filter (fun z=>expose L M R z=b) =
      jointFiber Set.univ X Xp W b.scales b.residue L (b.left R) (b.width R)
        b.pivotResidue M
 := by
  classical
  apply Finset.ext
  rintro ⟨t,p⟩
  simp only [rawDomain,Finset.product_eq_sprod,Finset.mem_filter,Finset.mem_product,Fintype.mem_piFinset,
    RawHarmonicProbability.units,Finset.mem_filter,jointFiber,rawTailFiber,Finset.product_eq_sprod,
    Set.mem_univ,true_and]
  constructor
  · rintro ⟨⟨ht,hp⟩,he⟩
    have htpos : ∀ j,0<t j := fun j=>(hX j).trans_le (Finset.mem_Ico.mp (ht j).1).1
    obtain ⟨hd,hrd,ha,hb⟩ := (expose_eq_iff L M R hR (t,p) htpos b hr ha).mp he
    exact ⟨⟨fun j=>⟨(ht j).1,(ht j).2,(hd j).1,(hd j).2,hrd j⟩,hp⟩,ha,hb⟩
  · rintro ⟨⟨ht,hp⟩,had,hb⟩
    have htpos : ∀ j,0<t j := fun j=>(hX j).trans_le (Finset.mem_Ico.mp (ht j).1).1
    refine ⟨⟨fun j=>⟨(ht j).1,(ht j).2.1⟩,hp⟩,?_⟩
    exact (expose_eq_iff L M R hR (t,p) htpos b hr ha).mpr
      ⟨fun j=>⟨(ht j).2.2.1,(ht j).2.2.2.1⟩,fun j=>(ht j).2.2.2.2,had,hb⟩

end ProductExposureLabels
end
end

section
noncomputable section
namespace ProductExposureCutoff
open DyadicHarmonicBoundary RawHarmonicProbability Finset Filter MeasureTheory
open scoped Topology BigOperators

def cutoff (X C : ℕ) : Set ℕ := {p | p ≤ 2^C*X ∨ X^2 ≤ 2^C*p}

lemma mass_mono_interval {A B C D W : ℕ} (hCA : C≤A) (hBD : B≤D) :
    mass A B W≤ mass C D W :=
  sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico hCA hBD) (by intros; positivity)

lemma many_dyadic_lower (X W K : ℕ) (hW : 0<W) (hX : 4*W≤X) :
    (K:ℝ)*((W.totient:ℝ)/(4*W))≤ mass X (X*2^K) W := by
  rw [mass,←dyadic_sum]
  calc
    _ = ∑ _k∈range K, (W.totient:ℝ)/(4*W) := by simp
    _ ≤ _ := by
      apply sum_le_sum
      intro k hk
      have hpow := Nat.one_le_pow k 2 (by omega)
      have hxk : 4*W≤X*2^k := by nlinarith
      have h := dyadic_lower (X*2^k) W hW hxk
      have hend : X*2^(k+1)=X*2^k+X*2^k := by rw [pow_succ]; ring
      simpa only [hend,mass] using h

lemma dyadic_upper_simple (Y W : ℕ) (hW : 0<W) (hY : 4*W≤Y) :
    mass Y (Y+Y) W≤ (3/2:ℝ)*((W.totient:ℝ)/W) := by
  have hw : (0:ℝ)<W := by exact_mod_cast hW
  have hy : (0:ℝ)<Y := by exact_mod_cast (show 0<Y by omega)
  have hY' : (4:ℝ)*W≤Y := by exact_mod_cast hY
  have hu := dyadic_upper Y W hW (by omega)
  have hd : 2*(W.totient:ℝ)/Y≤2*(W.totient:ℝ)/(4*W) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hY'
  calc
    _ ≤ (W.totient:ℝ)/W+2*W.totient/Y := hu
    _ ≤ (W.totient:ℝ)/W+2*W.totient/(4*W) := add_le_add_right hd _
    _ = _ := by ring

lemma many_dyadic_upper (X W K : ℕ) (hW : 0<W) (hX : 4*W≤X) :
    mass X (X*2^K) W≤(K:ℝ)*(3/2)*((W.totient:ℝ)/W) := by
  rw [mass,←dyadic_sum]
  calc
    _ ≤ ∑ _k∈range K, (3/2:ℝ)*((W.totient:ℝ)/W) := by
      apply sum_le_sum
      intro k hk
      have hpow := Nat.one_le_pow k 2 (by omega)
      have hxk : 4*W≤X*2^k := by nlinarith
      have h := dyadic_upper_simple (X*2^k) W hW hxk
      have hend : X*2^(k+1)=X*2^k+X*2^k := by rw [pow_succ]; ring
      simpa only [hend,mass] using h
    _ = _ := by simp; ring

lemma cutoff_mass_bound (X W C : ℕ) (hW : 0<W) (hX : 4*W≤X) (hCX : 2^C≤X) :
    MicrocellConditional.eventMass (units X W) (cutoff X C) ≤
      3*((C:ℝ)+1)*((W.totient:ℝ)/W) := by
  classical
  let A := X^2/2^C
  have hpow0 : 0<2^C := by positivity
  have hx : 0<X := by omega
  have hAx : X≤A := by
    dsimp [A]
    apply (Nat.le_div_iff_mul_le hpow0).mpr
    nlinarith
  have hA : 0<A := hx.trans_le hAx
  have hupper : X^2<A*2^(C+1) := by
    have hh := Nat.lt_div_mul_add (a:=X^2) hpow0
    change X^2<A*2^C+2^C at hh
    rw [pow_succ 2 C]
    nlinarith
  have hlower : 2^C*X<X*2^(C+1) := by rw [pow_succ 2 C]; nlinarith
  let E := (units X W).filter (·∈cutoff X C)
  have hE : MicrocellConditional.eventMass (units X W) (cutoff X C)=
      ∑ p∈E,(p:ℝ)⁻¹ := by simp [MicrocellConditional.eventMass,E,sum_filter]
  have hs₁ : E.filter (fun p=>p≤2^C*X) ⊆ (Ico X (X*2^(C+1))).filter W.Coprime := by
    intro p hp
    have hp₁ := mem_filter.mp hp
    have hp₂ := mem_filter.mp hp₁.1
    have hp₃ := mem_filter.mp hp₂.1
    have hlo := hp₁.2
    have hc := hp₂.2
    have hwp := hp₃.2
    obtain ⟨hxp,hpx⟩ := mem_Ico.mp hp₃.1
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨hxp,hlo.trans_lt hlower⟩,hwp⟩
  have hs₂ : E.filter (fun p=>¬p≤2^C*X) ⊆ (Ico A (A*2^(C+1))).filter W.Coprime := by
    intro p hp
    have hp₁ := mem_filter.mp hp
    have hp₂ := mem_filter.mp hp₁.1
    have hp₃ := mem_filter.mp hp₂.1
    have hlo := hp₁.2
    have hc := hp₂.2
    have hwp := hp₃.2
    obtain ⟨hxp,hpx⟩ := mem_Ico.mp hp₃.1
    have hc' : X^2≤2^C*p := (show p≤2^C*X ∨ X^2≤2^C*p from hc).resolve_left hlo
    have hap : A≤p := by
      dsimp [A]
      apply (Nat.div_le_iff_le_mul hpow0).mpr
      have hh : X^2≤p*2^C := by simpa only [mul_comm] using hc'
      omega
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨hap,hpx.trans hupper⟩,hwp⟩
  have hb₁ : (∑ p∈E.filter (fun p=>p≤2^C*X),(p:ℝ)⁻¹) ≤ mass X (X*2^(C+1)) W := by
    have h := sum_le_sum_of_subset_of_nonneg hs₁ (fun _ _ _=>by positivity : ∀ i∈(Ico X (X*2^(C+1))).filter W.Coprime, i∉E.filter (fun p=>p≤2^C*X) → 0≤(i:ℝ)⁻¹)
    simpa only [sum_filter,mass] using h
  have hb₂ : (∑ p∈E.filter (fun p=>¬p≤2^C*X),(p:ℝ)⁻¹) ≤ mass A (A*2^(C+1)) W := by
    have h := sum_le_sum_of_subset_of_nonneg hs₂ (fun _ _ _=>by positivity : ∀ i∈(Ico A (A*2^(C+1))).filter W.Coprime, i∉E.filter (fun p=>¬p≤2^C*X) → 0≤(i:ℝ)⁻¹)
    simpa only [sum_filter,mass] using h
  rw [hE,←sum_filter_add_sum_filter_not E (fun p=>p≤2^C*X)]
  have h₁ := many_dyadic_upper X W (C+1) hW hX
  have h₂ := many_dyadic_upper A W (C+1) hW (hX.trans hAx)
  push_cast at h₁ h₂
  linarith

 
theorem raw_cutoff_bound (X W C K : ℕ) (hW : 0<W) (hX : 4*W≤X)
    (hK : 0<K) (hKX : 2^K≤X) (hCX : 2^C≤X) :
    (law X W hW hX : Measure ℕ).real (cutoff X C) ≤
      12*((C:ℝ)+1)/K := by
  have ht : (0:ℝ)<W.totient := by exact_mod_cast Nat.totient_pos.mpr hW
  have hw : (0:ℝ)<W := by exact_mod_cast hW
  have hk : (0:ℝ)<K := by exact_mod_cast hK
  have hm := mass_pos X W hW hX
  have hl := (many_dyadic_lower X W K hW hX).trans
    (mass_mono (show X*2^K≤X^2 by nlinarith))
  rw [MicrocellConditional.law_apply_units]
  apply (div_le_iff₀ hm).mpr
  have hu := cutoff_mass_bound X W C hW hX hCX
  have hratio : 0≤12*((C:ℝ)+1)/K := by positivity
  have hh := mul_le_mul_of_nonneg_left hl hratio
  have he : (12*((C:ℝ)+1)/K)*((K:ℝ)*((W.totient:ℝ)/(4*W))) =
      3*((C:ℝ)+1)*((W.totient:ℝ)/W) := by field_simp; ring
  rw [he] at hh
  exact hu.trans hh

 
theorem raw_cutoff_decay (X W : ℕ→ℕ) (C : ℕ)
    (hW : ∀ n,0<W n) (hX : ∀ n,4*W n≤X n) (hXt : Tendsto X atTop atTop) :
    Tendsto (fun n=>(law (X n) (W n) (hW n) (hX n) : Measure ℕ).real
      (cutoff (X n) C)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun n=>ha.trans_le (measureReal_nonneg))
  · intro ε hε
    obtain ⟨K,hK⟩ := exists_nat_gt (12*((C:ℝ)+1)/ε)
    have hk : (0:ℝ)<K := lt_trans (by positivity) hK
    have hkN : 0<K := by exact_mod_cast hk
    have he : 12*((C:ℝ)+1)/K<ε := by
      have hh := (div_lt_iff₀ hε).mp hK
      exact (div_lt_iff₀ hk).mpr (by nlinarith)
    filter_upwards [hXt.eventually (eventually_ge_atTop (2^K)),
      hXt.eventually (eventually_ge_atTop (2^C))] with n hkn hcn
    exact (raw_cutoff_bound (X n) (W n) C K (hW n) (hX n) hkN hkn hcn).trans_lt he

end ProductExposureCutoff

end
end

end OAI
