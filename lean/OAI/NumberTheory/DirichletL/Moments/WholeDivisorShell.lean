import OAI.NumberTheory.DirichletL.Moments.MobiusRegroup
import OAI.NumberTheory.DirichletL.Moments.DyadicCount

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentWholeDivisorShell
open IdealMobiusDivisorSum UniqueFactorizationMonoid
open CenteredMomentMobiusRegroup CenteredMomentDyadicCount CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

lemma divisorPool_nonzero_norm {α : Type*} (T : Finset α) (B : α→Ideal O)
    (hB : ∀j∈T,B j≠0) (Y : ℝ) (hY : ∀j∈T,(Ideal.absNorm (B j):ℝ)≤Y)
    (D : Ideal O) (hD : D∈divisorPool T B) : D≠0 ∧ (D.absNorm:ℝ)≤Y := by
  obtain ⟨j,hj,hd⟩:=Finset.mem_biUnion.mp hD
  have hdiv := (mem_idealDivisors (hB j hj)).mp hd
  have hn : 0<(B j).absNorm := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hB j hj))
  have hle : (D.absNorm:ℝ)≤(B j).absNorm := by
    exact_mod_cast Nat.le_of_dvd hn (map_dvd Ideal.absNorm hdiv)
  exact ⟨IdealDivisorBound.divisor_ne_zero (hB j hj) hd,hle.trans (hY j hj)⟩

lemma moebius_norm_le_one (D : Ideal O) : ‖(moebius D:ℂ)‖≤1 := by
  by_cases hD : Squarefree D
  · simp only [hD.moebius_eq,Int.cast_pow,Int.cast_neg,Int.cast_one,norm_pow,norm_neg,norm_one,one_pow,le_refl]
  · simp only [moebius_of_not_squarefree hD,Int.cast_zero,norm_zero,zero_le_one]

lemma squarefree_of_moebius_ne_zero (D : Ideal O) (hD : (moebius D:ℂ)≠0) : Squarefree D := by
  by_contra hn
  exact hD (by rw [moebius_of_not_squarefree hn,Int.cast_zero])

def live (Ds : Finset (Ideal O)) : Finset (Ideal O) := Ds.filter (fun D=>(moebius D:ℂ)≠0)

lemma mem_live (Ds : Finset (Ideal O)) (D : Ideal O) :
    D∈live Ds ↔ D∈Ds ∧ (moebius D:ℂ)≠0 := Finset.mem_filter

lemma live_squarefree (Ds : Finset (Ideal O)) (D : Ideal O) (hD : D∈live Ds) : Squarefree D :=
  squarefree_of_moebius_ne_zero D ((mem_live Ds D).mp hD).2

lemma live_norm_one (Ds : Finset (Ideal O)) (D : Ideal O) (hD : D∈live Ds) : 1≤(D.absNorm:ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (live_squarefree Ds D hD).ne_zero)

theorem sum_moebius_live (Ds : Finset (Ideal O)) (f : Ideal O→ℂ) :
    (∑D∈Ds,(moebius D:ℂ)*f D)=∑D∈live Ds,(moebius D:ℂ)*f D := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro D hD hn
  have hz : (moebius D:ℂ)=0 := by
    by_contra hne
    exact hn ((mem_live Ds D).mpr ⟨hD,hne⟩)
  rw [hz,zero_mul]

theorem sum_norm_moebius_live (Ds : Finset (Ideal O)) (f : Ideal O→ℝ) :
    (∑D∈Ds,‖(moebius D:ℂ)‖*f D)=∑D∈live Ds,‖(moebius D:ℂ)‖*f D := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro D hD hn
  have hz : (moebius D:ℂ)=0 := by
    by_contra hne
    exact hn ((mem_live Ds D).mpr ⟨hD,hne⟩)
  rw [hz,norm_zero,zero_mul]

def normKey (D : Ideal O) : ℤ := ⌊Real.logb 2 (D.absNorm:ℝ)⌋
def shell (Ds : Finset (Ideal O)) (n : ℤ) : Finset (Ideal O) := (live Ds).filter (fun D=>normKey D=n)
def selectedShells (Ds : Finset (Ideal O)) : Finset ℤ := (live Ds).image normKey

lemma normKey_eq_iff (D : Ideal O) (hD : D≠0) (n : ℤ) :
    normKey D=n ↔ dyadicScale n≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*dyadicScale n := by
  have hn : 0<(D.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hl := Real.logb_le_logb (by norm_num : (1:ℝ)<2) (dyadicScale_pos n) hn
  have hu := Real.logb_lt_logb_iff (by norm_num : (1:ℝ)<2) hn (dyadicScale_pos (n+1))
  simp only [logb_dyadicScale,Int.cast_add,Int.cast_one] at hl hu
  rw [normKey,Int.floor_eq_iff,←hl,←dyadicScale_add,←hu]

lemma mem_shell_iff (Ds : Finset (Ideal O)) (n : ℤ) (D : Ideal O) :
    D∈shell Ds n ↔ D∈Ds ∧ (moebius D:ℂ)≠0 ∧
      dyadicScale n≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*dyadicScale n := by
  rw [shell,Finset.mem_filter]
  constructor
  · rintro ⟨hd,hk⟩
    exact ⟨((mem_live Ds D).mp hd).1,((mem_live Ds D).mp hd).2,
      (normKey_eq_iff D (live_squarefree Ds D hd).ne_zero n).mp hk⟩
  · rintro ⟨hd,hm,hlo,hhi⟩
    exact ⟨(mem_live Ds D).mpr ⟨hd,hm⟩,
      (normKey_eq_iff D (squarefree_of_moebius_ne_zero D hm).ne_zero n).mpr ⟨hlo,hhi⟩⟩

lemma shell_disjoint (Ds : Finset (Ideal O)) (m n : ℤ) (hmn : m≠n) :
    Disjoint (shell Ds m) (shell Ds n) := by
  apply Finset.disjoint_left.mpr
  intro D hm hn
  exact hmn ((Finset.mem_filter.mp hm).2.symm.trans (Finset.mem_filter.mp hn).2)

lemma shell_nonempty_iff (Ds : Finset (Ideal O)) (n : ℤ) :
    (shell Ds n).Nonempty ↔ n∈selectedShells Ds := by
  constructor
  · rintro ⟨D,hD⟩
    exact Finset.mem_image.mpr ⟨D,(Finset.mem_filter.mp hD).1,(Finset.mem_filter.mp hD).2⟩
  · rintro hn
    obtain ⟨D,hD,hk⟩:=Finset.mem_image.mp hn
    exact ⟨D,Finset.mem_filter.mpr ⟨hD,hk⟩⟩

lemma biUnion_shell (Ds : Finset (Ideal O)) :
    (selectedShells Ds).biUnion (shell Ds)=live Ds := by
  ext D
  simp only [Finset.mem_biUnion,shell,Finset.mem_filter]
  constructor
  · rintro ⟨n,hn,hd,hk⟩;exact hd
  · intro hd
    exact ⟨normKey D,Finset.mem_image.mpr ⟨D,hd,rfl⟩,hd,rfl⟩

theorem sum_moebius_shells (Ds : Finset (Ideal O)) (f : Ideal O→ℂ) :
    (∑D∈Ds,(moebius D:ℂ)*f D)=
      ∑n∈selectedShells Ds,∑D∈shell Ds n,(moebius D:ℂ)*f D := by
  rw [sum_moebius_live]
  exact (Finset.sum_fiberwise_of_maps_to (fun D hD=>Finset.mem_image.mpr ⟨D,hD,rfl⟩) _).symm

theorem sum_norm_moebius_shells (Ds : Finset (Ideal O)) (f : Ideal O→ℝ) :
    (∑D∈Ds,‖(moebius D:ℂ)‖*f D)=
      ∑n∈selectedShells Ds,∑D∈shell Ds n,‖(moebius D:ℂ)‖*f D := by
  rw [sum_norm_moebius_live]
  exact (Finset.sum_fiberwise_of_maps_to (fun D hD=>Finset.mem_image.mpr ⟨D,hD,rfl⟩) _).symm

lemma selected_scale_bounds (Ds : Finset (Ideal O)) (Y : ℝ)
    (hY : ∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Y)
    (n : ℤ) (hn : n∈selectedShells Ds) :
    1≤dyadicScale n ∧ dyadicScale n≤Y := by
  obtain ⟨D,hD,rfl⟩:=Finset.mem_image.mp hn
  have hd:=live_squarefree Ds D hD
  have hnorm:=live_norm_one Ds D hD
  have hkey : 0≤normKey D := Int.floor_nonneg.mpr
    (Real.logb_nonneg (by norm_num : (1:ℝ)<2) hnorm)
  have hscale : 1≤dyadicScale (normKey D) := by
    simpa only [dyadicScale,zpow_zero] using
      zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2) hkey
  exact ⟨hscale,((normKey_eq_iff D hd.ne_zero _).mp rfl).1.trans
    (hY D ((mem_live Ds D).mp hD).1 ((mem_live Ds D).mp hD).2)⟩

lemma selected_subset_indices (Ds : Finset (Ideal O)) (Y : ℝ) (hY : 1≤Y)
    (hbound : ∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Y) :
    selectedShells Ds⊆indices 1 Y := by
  intro n hn
  have hh:=selected_scale_bounds Ds Y hbound n hn
  exact (mem_indices_iff_scale 1 Y (by norm_num) (zero_lt_one.trans_le hY) n).mpr
    ⟨hh.1,hh.2.trans (by linarith)⟩

theorem selected_card_log (B Z : ℝ) (hB : 0≤B) (hZ : 1≤Z)
    (Ds : Finset (Ideal O))
    (hbound : ∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^B) :
    ((selectedShells Ds).card:ℝ)≤(3+B/Real.log 2)*(1+Real.log Z) := by
  have hY : 1≤Z^B := Real.one_le_rpow hZ hB
  have hc : ((selectedShells Ds).card:ℝ)≤(indices 1 (Z^B)).card := by
    exact_mod_cast Finset.card_le_card (selected_subset_indices Ds (Z^B) hY hbound)
  have hi:=indices_card_log_bound 1 B Z 1 (Z^B) le_rfl hB hZ (by norm_num) hY
    (by simp only [div_one,one_mul,le_refl])
  exact hc.trans (by simpa only [Real.logb_one,add_zero] using hi)

theorem selected_card_subpower (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Ds:Finset (Ideal O),
      (∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^B) →
      ((selectedShells Ds).card:ℝ)≤C*Z^δ := by
  let C:=2*(3+B/Real.log 2)
  have hC : 0<C := by
    have hh:=div_nonneg hB (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    dsimp [C];linarith
  have ht:=(isLittleO_log_rpow_rpow_atTop (1:ℝ) hδ).bound (by norm_num : (0:ℝ)<1)
  refine ⟨C,hC,?_⟩
  filter_upwards [ht,eventually_ge_atTop (Real.exp 1)] with Z ht hZ
  have hz : 1<Z := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hZ
  have hl : 1≤Real.log Z := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hZ
  have hp : Real.log Z≤Z^δ := by
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤Real.log Z),
      abs_of_nonneg (Real.rpow_nonneg (zero_lt_one.trans hz).le _),one_mul] using ht
  refine ⟨hz,?_⟩
  intro Ds hb
  apply (selected_card_log B Z hB hz.le Ds hb).trans
  have hk : 0≤3+B/Real.log 2 := by positivity
  dsimp [C]
  nlinarith [mul_le_mul_of_nonneg_left hp hk]

theorem divisorPool_card_log {α : Type*} (T : Finset α) (B : α→Ideal O)
    (hB : ∀j∈T,B j≠0) (L Z : ℝ) (hL : 0≤L) (hZ : 1≤Z)
    (hN : ∀j∈T,(Ideal.absNorm (B j):ℝ)≤Z^L) :
    ((selectedShells (divisorPool T B)).card:ℝ)≤(3+L/Real.log 2)*(1+Real.log Z) :=
  selected_card_log L Z hL hZ _ (fun D hD _=>(divisorPool_nonzero_norm T B hB _ hN D hD).2)

theorem divisorPool_card_subpower (L δ : ℝ) (hL : 0≤L) (hδ : 0<δ) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{α:Type*}(T:Finset α)(B:α→Ideal O),
      (∀j∈T,B j≠0) → (∀j∈T,(Ideal.absNorm (B j):ℝ)≤Z^L) →
      ((selectedShells (divisorPool T B)).card:ℝ)≤C*Z^δ := by
  obtain ⟨C,hC,hbound⟩:=selected_card_subpower L δ hL hδ
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro α T B hB hN
  exact hz.2 _ (fun D hD _=>(divisorPool_nonzero_norm T B hB _ hN D hD).2)

lemma shell_member_data (Ds : Finset (Ideal O)) (n : ℤ) (D : Ideal O)
    (hD : D∈shell Ds n) :
    D∈Ds ∧ (moebius D:ℂ)≠0 ∧ Squarefree D ∧ D≠0 ∧
      dyadicScale n≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*dyadicScale n := by
  have hh:=(mem_shell_iff Ds n D).mp hD
  have hs:=squarefree_of_moebius_ne_zero D hh.2.1
  exact ⟨hh.1,hh.2.1,hs,hs.ne_zero,hh.2.2⟩

theorem finite_pair_mobius_shells {α β : Type*} (S : Finset α) (T : Finset β)
    (A : α→Ideal O) (B : β→Ideal O) (hB : ∀j∈T,B j≠0) (F : α→β→ℂ) :
    (∑i∈S,∑j∈T,if IsCoprime (A i) (B j) then F i j else 0)=
      ∑n∈selectedShells (divisorPool T B),∑D∈shell (divisorPool T B) n,
        (moebius D:ℂ)*∑i∈S,∑j∈T,if D∣A i ∧ D∣B j then F i j else 0 := by
  rw [finite_pair_mobius S T A B hB F]
  exact sum_moebius_shells _ _

theorem divisorPool_weighted_shells {α : Type*} (T : Finset α) (B : α→Ideal O)
    (f : Ideal O→ℝ) :
    (∑D∈divisorPool T B,‖(moebius D:ℂ)‖*f D)=
      ∑n∈selectedShells (divisorPool T B),∑D∈shell (divisorPool T B) n,
        ‖(moebius D:ℂ)‖*f D := sum_norm_moebius_shells _ _

end SevenEighths.CenteredMomentWholeDivisorShell

end

end OAI
