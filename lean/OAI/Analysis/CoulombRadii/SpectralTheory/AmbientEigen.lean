import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.SortedCut
import OAI.Analysis.CoulombRadii.SpectralTheory.SectorBottomBridge
import OAI.Analysis.CoulombRadii.FormDomain.H1Pairing

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical
noncomputable section
namespace Coulomb
lemma massPair_congr {n:ℕ} (u v u' v':H1Vector n)
    (hu:∀ s,u.value s=ᵐ[volume]u'.value s) (hv:∀ s,v.value s=ᵐ[volume]v'.value s) :
    massPair u v=massPair u' v' := by
  unfold massPair
  apply Finset.sum_congr rfl
  intro s _
  apply integral_congr_ae
  filter_upwards [hu s,hv s] with x hx hy
  rw [hx,hy]
lemma formPair_congr {M n:ℕ} (S:Nuclei M) (u v u' v':H1Vector n)
    (hu:∀ s,u.value s=ᵐ[volume]u'.value s) (hv:∀ s,v.value s=ᵐ[volume]v'.value s) :
    formPair S u v=formPair S u' v' := by
  have he:∀ s,(u.add v).value s=ᵐ[volume](u'.add v').value s:=fun s => (hu s).add (hv s)
  have hh:=form_congr_ae S (u.add v) (u'.add v') he
  linarith [formPair_polarization S u v,formPair_polarization S u' v',form_congr_ae S u u' hu,form_congr_ae S v v' hv]
lemma massPair_symm {n:ℕ} (u v:H1Vector n) : massPair u v=massPair v u := by
  simp only [massPair,real_inner_comm]
lemma formPair_symm {M n:ℕ} (S:Nuclei M) (u v:H1Vector n) : formPair S u v=formPair S v u := by
  simp only [formPair,kineticPair,nuclearPair,repulsionPair,real_inner_comm]
lemma massPair_rsmul_right {n:ℕ} (u v:H1Vector n) (t:ℝ) : massPair u (v.rsmul t)=t*massPair u v := by
  simp only [massPair,H1Vector.rsmul,←Complex.real_smul,real_inner_smul_right,integral_const_mul,Finset.mul_sum]
lemma formPair_rsmul_right {M n:ℕ} (S:Nuclei M) (u v:H1Vector n) (t:ℝ) :
    formPair S u (v.rsmul t)=t*formPair S u v := by
  unfold formPair kineticPair nuclearPair repulsionPair
  simp only [H1Vector.rsmul,←Complex.real_smul,real_inner_smul_right]
  simp_rw [mul_left_comm _ t,integral_const_mul,←Finset.mul_sum]
  ring
lemma massPair_rsmul_left {n:ℕ} (u v:H1Vector n) (t:ℝ) : massPair (u.rsmul t) v=t*massPair u v := by
  rw [massPair_symm,massPair_rsmul_right,massPair_symm v u]
lemma formPair_rsmul_left {M n:ℕ} (S:Nuclei M) (u v:H1Vector n) (t:ℝ) :
    formPair S (u.rsmul t) v=t*formPair S u v := by
  rw [formPair_symm,formPair_rsmul_right,formPair_symm S v u]
lemma massPair_permutation {n:ℕ} (u v:H1Vector n) (p:Equiv.Perm (Fin n)) :
    massPair (u.permutation p) (v.permutation p)=massPair u v := by
  have he:∀ s,((u.add v).permutation p).value s=ᵐ[volume]((u.permutation p).add (v.permutation p)).value s :=
    fun s => Eventually.of_forall fun x => by simp only [permutation_value,H1Vector.add]
  have hh:=mass_congr_ae _ _ he
  rw [mass_permutation] at hh
  have h:=massPair_polarization (u.permutation p) (v.permutation p)
  rw [mass_permutation,mass_permutation,←hh] at h
  linarith [massPair_polarization u v]
lemma formPair_permutation {M n:ℕ} (S:Nuclei M) (u v:H1Vector n) (p:Equiv.Perm (Fin n)) :
    formPair S (u.permutation p) (v.permutation p)=formPair S u v := by
  have he:∀ s,((u.add v).permutation p).value s=ᵐ[volume]((u.permutation p).add (v.permutation p)).value s :=
    fun s => Eventually.of_forall fun x => by simp only [permutation_value,H1Vector.add]
  have hh:=form_congr_ae S _ _ he
  rw [form_permutation] at hh
  have h:=formPair_polarization S (u.permutation p) (v.permutation p)
  rw [form_permutation,form_permutation,←hh] at h
  linarith [formPair_polarization S u v]
lemma massPair_finiteSum {n:ℕ} {ι:Type*} [Fintype ι] (u:H1Vector n) (v:ι → H1Vector n) :
    massPair u (H1Vector.finiteSum v)=∑ i,massPair u (v i) := by
  unfold massPair
  simp only [H1Vector.finiteSum,inner_sum]
  simp_rw [integral_finsetSum _ (fun i _ => memlp_real_inner_integrable (u.value_L2 _) ((v i).value_L2 _))]
  exact Finset.sum_comm
lemma formPair_finiteSum {M n:ℕ} {ι:Type*} [Fintype ι] (S:Nuclei M) (u:H1Vector n) (v:ι → H1Vector n) :
    formPair S u (H1Vector.finiteSum v)=∑ i,formPair S u (v i) := by
  have hT:kineticPair u (H1Vector.finiteSum v)=∑ i,kineticPair u (v i) := by
    unfold kineticPair
    simp only [H1Vector.finiteSum,inner_sum]
    simp_rw [integral_finsetSum _ (fun i _ => formPair_kinetic_integrable u (v i) _ _)]
    rw [←Finset.mul_sum]
    congr 1
    calc
      _ = ∑ s,∑ i,∑ a,∫ x,inner ℝ (u.gradient s a x) ((v i).gradient s a x) :=
        Finset.sum_congr rfl (fun s _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  have hN:nuclearPair S u (H1Vector.finiteSum v)=∑ i,nuclearPair S u (v i) := by
    unfold nuclearPair
    simp only [H1Vector.finiteSum,inner_sum,Finset.mul_sum]
    simp_rw [integral_finsetSum _ (fun i _ => formPair_nuclear_integrable S u (v i) _)]
    exact Finset.sum_comm
  have hP:repulsionPair u (H1Vector.finiteSum v)=∑ i,repulsionPair u (v i) := by
    unfold repulsionPair
    simp only [H1Vector.finiteSum,inner_sum,Finset.mul_sum]
    simp_rw [integral_finsetSum _ (fun i _ => formPair_repulsion_integrable u (v i) _)]
    exact Finset.sum_comm
  simp only [formPair,hT,hN,hP,Finset.sum_add_distrib,Finset.sum_sub_distrib]

lemma sector_minimizer_ambient_eigen (Z:ℕ) (hZ:1 ≤ Z) {n:ℕ}
    (u:H1Vector n) (ha:Antisymmetric u) (hm:mass u=1)
    (hmin:(form (atom Z hZ) u:EReal)=sectorFormBottom (atom Z hZ) n)
    (v:H1Vector n) :
    formPair (atom Z hZ) u v=form (atom Z hZ) u*massPair u v := by
  let sign:=fun p:Equiv.Perm (Fin n) => ((p.sign:ℤ):ℝ)
  let av:=H1Vector.finiteSum (fun p:Equiv.Perm (Fin n) => (v.permutation p).rsmul (sign p))
  have he:∀ s,av.value s=ᵐ[volume]v.fullAntisymmetrize.value s:= by
    intro s
    exact Eventually.of_forall fun x => by simp [av,fullAntisymmetrize_value,H1Vector.finiteSum,H1Vector.rsmul,sign,permutation_value]
  have hav:Antisymmetric av := by
    intro p s
    filter_upwards [he (s ∘ p) |>.comp_tendsto (permute_measurePreserving p).quasiMeasurePreserving.tendsto_ae,
      he s,fullAntisymmetrize_antisymmetric v p s] with x hx hy hz
    dsimp only [Function.comp_apply] at hx
    rw [hx,hz,←hy]
  have hp(p:Equiv.Perm (Fin n)):∀ s,(u.permutation p).value s=ᵐ[volume](u.rsmul (sign p)).value s := by
    intro s
    filter_upwards [ha p s] with x hx
    simpa only [permutation_value,H1Vector.rsmul,sign,Complex.ofReal_intCast] using hx
  have hform:formPair (atom Z hZ) u av=(Fintype.card (Equiv.Perm (Fin n)):ℝ)*formPair (atom Z hZ) u v := by
    rw [formPair_finiteSum]
    calc
      _ = ∑ _p:Equiv.Perm (Fin n),formPair (atom Z hZ) u v := by
        apply Finset.sum_congr rfl
        intro p _
        rw [formPair_rsmul_right,←formPair_rsmul_left]
        rw [←formPair_congr (atom Z hZ) (u.permutation p) (v.permutation p) _ _ (hp p) (fun _ => EventuallyEq.rfl)]
        exact formPair_permutation _ _ _ _
      _ = _ := by simp
  have hmass:massPair u av=(Fintype.card (Equiv.Perm (Fin n)):ℝ)*massPair u v := by
    rw [massPair_finiteSum]
    calc
      _ = ∑ _p:Equiv.Perm (Fin n),massPair u v := by
        apply Finset.sum_congr rfl
        intro p _
        rw [massPair_rsmul_right,←massPair_rsmul_left]
        rw [←massPair_congr (u.permutation p) (v.permutation p) _ _ (hp p) (fun _ => EventuallyEq.rfl)]
        exact massPair_permutation _ _ _
      _ = _ := by simp
  have H:=sector_minimizer_weak_eigen Z hZ u ha hm hmin av hav
  rw [hform,hmass] at H
  have hc:0<(Fintype.card (Equiv.Perm (Fin n)):ℝ):=by exact_mod_cast Fintype.card_pos
  nlinarith
end Coulomb
end

end
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb
lemma inner_double_real (a:ℂ) (f:ℝ) :
    inner ℝ a ((f:ℂ)*((f:ℂ)*a))=‖(f:ℂ)*a‖^2 := by
  simp only [←Complex.real_smul,real_inner_smul_right,real_inner_self_eq_norm_sq,
    norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring
lemma weighted_core_inequality (Z:ℕ) (hZ:1≤Z) {k:ℕ}
    (u:H1Vector (1+k)) (ha:Antisymmetric u) (hm:mass u=1)
    (hmin:(form (atom Z hZ) u:EReal)=sectorFormBottom (atom Z hZ) (1+k))
    (f:Configuration (1+k) → ℝ) (hf:ContDiff ℝ ∞ f)
    (B D:ℝ) (hB:∀ x,|f x|≤B)
    (hD:∀ a x,|fderiv ℝ f x (EuclideanSpace.single a 1)|≤D)
    (hcore:∀ (a:Fin k × Fin 3) x,fderiv ℝ f x (EuclideanSpace.single (Fin.natAdd 1 a.1,a.2) 1)=0)
    (hperm:∀ (p:Equiv.Perm (Fin k)) x,f (permute (corePerm 1 p) x)=f x)
    (hkin:let z:=u.smoothMul f hf B D hB hD
      let v:=z.smoothMul f hf B D hB hD
      0≤∑ s,∑ a:Fin 3,∫ x,inner ℝ (u.gradient s (0,a) x) (v.gradient s (0,a) x)) :
    let z:=u.smoothMul f hf B D hB hD
    potentialForm (fun x => crossPotential ((joinConfiguration 1 k).symm x).1
      ((joinConfiguration 1 k).symm x).2) z ≤
      potentialForm (fun x => nuclearPotential (atom Z hZ) ((joinConfiguration 1 k).symm x).1) z := by
  let z:=u.smoothMul f hf B D hB hD
  let v:=z.smoothMul f hf B D hB hD
  have hi(s:Spins (1+k))(x:Configuration (1+k)):
      inner ℝ (u.value s x) (v.value s x)=‖z.value s x‖^2:=inner_double_real _ _
  have hmz:massPair u v=mass z := by simp only [massPair,mass,hi]
  have hnz:nuclearPair (atom Z hZ) u v=nuclearEnergy (atom Z hZ) z := by
    simp only [nuclearPair,nuclearEnergy,hi]
  have hpz:repulsionPair u v=pairEnergy z := by simp only [repulsionPair,pairEnergy,hi,pairPotential]
  have hg(s:Spins (1+k))(a:Fin k × Fin 3)(x:Configuration (1+k)):
      inner ℝ (u.gradient s (Fin.natAdd 1 a.1,a.2) x)
        (v.gradient s (Fin.natAdd 1 a.1,a.2) x)=
        ‖z.gradient s (Fin.natAdd 1 a.1,a.2) x‖^2 := by
    simp only [v,z,H1Vector.smoothMul,hcore,Complex.ofReal_zero,zero_mul,zero_add]
    exact inner_double_real _ _
  have hk:kineticPair u v=coreKinetic z+
      (1/2:ℝ)*(∑ s,∑ a:Fin 3,∫ x,inner ℝ (u.gradient s (0,a) x) (v.gradient s (0,a) x)) := by
    unfold kineticPair coreKinetic
    simp only [Fintype.sum_prod_type,Fin.sum_univ_add,Fin.sum_univ_one,Finset.sum_add_distrib]
    have hg' (s:Spins (1+k))(i:Fin k)(a:Fin 3)(x:Configuration (1+k)) := hg s (i,a) x
    simp only [hg',show Fin.castAdd k (0:Fin 1)=(0:Fin (1+k)) from rfl]
    ring
  have he:=sector_minimizer_ambient_eigen Z hZ u ha hm hmin v
  rw [formPair,hk,hnz,hpz,hmz] at he
  have hanti:∀ s:Spins 1,∀ᵐ x,Antisymmetric (z.coreSlice s x) := by
    intro s
    apply z.coreSlice_antisymmetric
    intro p t
    filter_upwards [ha (corePerm 1 p) (Fin.append s t)] with x hx
    change (f (permute (corePerm 1 p) x):ℂ)*u.value _ (permute (corePerm 1 p) x)=_
    rw [hperm,hx]
    change (f x:ℂ)*(_*u.value _ x)=_ *((f x:ℂ)*u.value _ x)
    ring
  have hs:=slice_core_form_ge_sector (atom Z hZ) z hanti
    (P:=form (atom Z hZ) u)
    (hmin.le.trans (atom_sectorFormBottom_antitone Z hZ (by omega : k≤1+k)))
  change _≤∑ s:Spins 1,∫ x,mass (z.coreSlice s x)*form (atom Z hZ) (z.coreSlice s x).normalized at hs
  rw [conditional_core_form_identity] at hs
  rw [nuclearEnergy_split,pairEnergy_split] at he
  have houter:0≤potentialForm (fun x => pairPotential ((joinConfiguration 1 k).symm x).1) z := by
    apply Finset.sum_nonneg
    intro s _
    exact integral_nonneg fun x => mul_nonneg (by
      unfold pairPotential
      apply Finset.sum_nonneg
      intro i _
      apply Finset.sum_nonneg
      intro j _
      split_ifs
      · exact inv_nonneg.mpr (norm_nonneg _)
      · rfl) (sq_nonneg _)
  dsimp only at hkin ⊢
  change _≤_
  linarith only [he,hs,houter,hkin]
end Coulomb
end

end

end OAI
