import OAI.InformationTheory.BooleanNoise.CurvatureCertificates
import OAI.InformationTheory.BooleanNoise.InverseRegularity
import OAI.InformationTheory.SoftChannel.EndpointLimits

namespace OAI

section

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

def CurvatureCertificates_curvatureBernstein : Fin 19 → ℝ :=
  ![(4591 / 62500 : ℝ),
    (49876 / 703125 : ℝ),
    (616620509 / 9036562500 : ℝ),
    (425343109 / 6506325000 : ℝ),
    (1239780551 / 19880437500 : ℝ),
    (8677345901149 / 146538704812500 : ℝ),
    (243668974553 / 4355288437500 : ℝ),
    (9012669336346771 / 171450284630625000 : ℝ),
    (1633213857973883 / 33281525840062500 : ℝ),
    (270017981574109469 / 5940752362451156250 : ℝ),
    (49027630438590434159 / 1176268967765328937500 : ℝ),
    (363078011510202773129 / 9624018827170873125000 : ℝ),
    (10171907529149910232987 / 303156593055882503437500 : ℝ),
    (4117638512237582389 / 141331745014397437500 : ℝ),
    (29341211329970780039 / 1199300807693601112500 : ℝ),
    (7749647417493214337891 / 395769266538888367125000 : ℝ),
    (14423931694547701552427 / 989423166347220917812500 : ℝ),
    (140069602865401114033 / 14550340681576778203125 : ℝ),
    (2753371080520712929 / 554298692631496312500 : ℝ)]

theorem CurvatureCertificates_curvatureBernstein_pos (i : Fin 19) : 0 < CurvatureCertificates_curvatureBernstein i := by
  fin_cases i <;> norm_num [CurvatureCertificates_curvatureBernstein]

def CurvatureCertificates_curvatureChunk0 (t : ℝ) : ℝ :=
  (4591 / 62500 : ℝ) * (1 : ℝ) * t ^ 0 * (1-t) ^ 18 +(49876 / 703125 : ℝ) * (18 : ℝ) * t ^ 1 * (1-t) ^ 17 +(616620509 / 9036562500 : ℝ) * (153 : ℝ) * t ^ 2 * (1-t) ^ 16 +(425343109 / 6506325000 : ℝ) * (816 : ℝ) * t ^ 3 * (1-t) ^ 15 +(1239780551 / 19880437500 : ℝ) * (3060 : ℝ) * t ^ 4 * (1-t) ^ 14

def CurvatureCertificates_curvatureExpanded0 (t : ℝ) : ℝ :=
  (4591 / 62500 : ℝ) * t ^ 0 +
      (-7091 / 156250 : ℝ) * t ^ 1 +
      (-80123 / 2953125 : ℝ) * t ^ 2 +
      (4396034 / 398671875 : ℝ) * t ^ 3 +
      (665564 / 292359375 : ℝ) * t ^ 4 +
      (-21190077014 / 41765625 : ℝ) * t ^ 5 +
      (3481363453321 / 626484375 : ℝ) * t ^ 6 +
      (-1202154535478 / 41765625 : ℝ) * t ^ 7 +
      (3523885857661 / 37968750 : ℝ) * t ^ 8 +
      (-16505912944859 / 79734375 : ℝ) * t ^ 9 +
      (2979568874243 / 8859375 : ℝ) * t ^ 10 +
      (-18099037012498 / 44296875 : ℝ) * t ^ 11 +
      (4274088181922 / 11390625 : ℝ) * t ^ 12 +
      (-4939200917498 / 18984375 : ℝ) * t ^ 13 +
      (510258530647 / 3796875 : ℝ) * t ^ 14 +
      (-1258664754982 / 25059375 : ℝ) * t ^ 15 +
      (75162420503017 / 5847187500 : ℝ) * t ^ 16 +
      (-47199998281 / 23388750 : ℝ) * t ^ 17 +
      (643419989006 / 4385390625 : ℝ) * t ^ 18

lemma CurvatureCertificates_curvatureChunk0_eq (t : ℝ) : CurvatureCertificates_curvatureChunk0 t=CurvatureCertificates_curvatureExpanded0 t := by
  unfold CurvatureCertificates_curvatureChunk0 CurvatureCertificates_curvatureExpanded0
  ring

def CurvatureCertificates_curvatureChunk1 (t : ℝ) : ℝ :=
  (8677345901149 / 146538704812500 : ℝ) * (8568 : ℝ) * t ^ 5 * (1-t) ^ 13 +(243668974553 / 4355288437500 : ℝ) * (18564 : ℝ) * t ^ 6 * (1-t) ^ 12 +(9012669336346771 / 171450284630625000 : ℝ) * (31824 : ℝ) * t ^ 7 * (1-t) ^ 11 +(1633213857973883 / 33281525840062500 : ℝ) * (43758 : ℝ) * t ^ 8 * (1-t) ^ 10 +(270017981574109469 / 5940752362451156250 : ℝ) * (48620 : ℝ) * t ^ 9 * (1-t) ^ 9

def CurvatureCertificates_curvatureExpanded1 (t : ℝ) : ℝ :=
  (17354691802298 / 34206046875 : ℝ) * t ^ 5 +
      (-950420284700233 / 171030234375 : ℝ) * t ^ 6 +
      (4771358404978582 / 165767765625 : ℝ) * t ^ 7 +
      (-857160603363297823 / 9235632656250 : ℝ) * t ^ 8 +
      (252941709148261987031 / 1221874200421875 : ℝ) * t ^ 9 +
      (-18362979380827089383 / 54305520018750 : ℝ) * t ^ 10 +
      (286444817585035096264 / 678819000234375 : ℝ) * t ^ 11 +
      (-170287429402159339 / 406884515625 : ℝ) * t ^ 12 +
      (33027763533426162188 / 96974142890625 : ℝ) * t ^ 13 +
      (-4426061793805223332 / 19394828578125 : ℝ) * t ^ 14 +
      (7016317227043613942 / 58184485734375 : ℝ) * t ^ 15 +
      (-62397657252485608649 / 1357638000468750 : ℝ) * t ^ 16 +
      (27028693110521981 / 2468432728125 : ℝ) * t ^ 17 +
      (-14713644059062616159 / 12218742004218750 : ℝ) * t ^ 18

lemma CurvatureCertificates_curvatureChunk1_eq (t : ℝ) : CurvatureCertificates_curvatureChunk1 t=CurvatureCertificates_curvatureExpanded1 t := by
  unfold CurvatureCertificates_curvatureChunk1 CurvatureCertificates_curvatureExpanded1
  ring

def CurvatureCertificates_curvatureChunk2 (t : ℝ) : ℝ :=
  (49027630438590434159 / 1176268967765328937500 : ℝ) * (43758 : ℝ) * t ^ 10 * (1-t) ^ 8 +(363078011510202773129 / 9624018827170873125000 : ℝ) * (31824 : ℝ) * t ^ 11 * (1-t) ^ 7 +(10171907529149910232987 / 303156593055882503437500 : ℝ) * (18564 : ℝ) * t ^ 12 * (1-t) ^ 6 +(4117638512237582389 / 141331745014397437500 : ℝ) * (8568 : ℝ) * t ^ 13 * (1-t) ^ 5 +(29341211329970780039 / 1199300807693601112500 : ℝ) * (3060 : ℝ) * t ^ 14 * (1-t) ^ 4

def CurvatureCertificates_curvatureExpanded2 (t : ℝ) : ℝ :=
  (49027630438590434159 / 26881232409281250 : ℝ) * t ^ 10 +
      (-8098817455925872602362 / 604827729208828125 : ℝ) * t ^ 11 +
      (12852516598885755400633 / 296915430702515625 : ℝ) * t ^ 12 +
      (-62530690738860041913986 / 777635651839921875 : ℝ) * t ^ 13 +
      (131322976750331117820161 / 1399744173311859375 : ℝ) * t ^ 14 +
      (-689559766180042758734306 / 9798209213183015625 : ℝ) * t ^ 15 +
      (541378823206442623169759 / 16330348688638359375 : ℝ) * t ^ 16 +
      (-17588415841001370441862 / 1959641842636603125 : ℝ) * t ^ 17 +
      (104976412464057351032771 / 97982092131830156250 : ℝ) * t ^ 18

lemma CurvatureCertificates_curvatureChunk2_eq (t : ℝ) : CurvatureCertificates_curvatureChunk2 t=CurvatureCertificates_curvatureExpanded2 t := by
  unfold CurvatureCertificates_curvatureChunk2 CurvatureCertificates_curvatureExpanded2
  ring

def CurvatureCertificates_curvatureChunk3 (t : ℝ) : ℝ :=
  (7749647417493214337891 / 395769266538888367125000 : ℝ) * (816 : ℝ) * t ^ 15 * (1-t) ^ 3 +(14423931694547701552427 / 989423166347220917812500 : ℝ) * (153 : ℝ) * t ^ 16 * (1-t) ^ 2 +(140069602865401114033 / 14550340681576778203125 : ℝ) * (18 : ℝ) * t ^ 17 * (1-t) ^ 1 +(2753371080520712929 / 554298692631496312500 : ℝ) * (1 : ℝ) * t ^ 18 * (1-t) ^ 0

def CurvatureCertificates_curvatureExpanded3 (t : ℝ) : ℝ :=
  (15499294834986428675782 / 970022712105118546875 : ℝ) * t ^ 15 +
      (-98520655001726957321071 / 2155606026900263437500 : ℝ) * t ^ 16 +
      (268817704889101313641 / 6158874362572181250 : ℝ) * t ^ 17 +
      (-7499427891584357517851 / 538901506725065859375 : ℝ) * t ^ 18

lemma CurvatureCertificates_curvatureChunk3_eq (t : ℝ) : CurvatureCertificates_curvatureChunk3 t=CurvatureCertificates_curvatureExpanded3 t := by
  unfold CurvatureCertificates_curvatureChunk3 CurvatureCertificates_curvatureExpanded3
  ring

def CurvatureCertificates_lambdaBernsteinLow : Fin 9 → ℝ :=
  ![4,
    (241 / 64 : ℝ),
    (1537 / 448 : ℝ),
    (42755 / 14336 : ℝ),
    (217187 / 89600 : ℝ),
    (510487 / 286720 : ℝ),
    (8901163 / 8028160 : ℝ),
    (19161827 / 36700160 : ℝ),
    (1316227 / 4587520 : ℝ)]

def CurvatureCertificates_lambdaBernsteinHigh : Fin 9 → ℝ :=
  ![(1316227 / 4587520 : ℝ),
    (7652479 / 36700160 : ℝ),
    (5432143 / 32112640 : ℝ),
    (2869523 / 16056320 : ℝ),
    (3747241 / 15052800 : ℝ),
    (1185781 / 3010560 : ℝ),
    (79071 / 125440 : ℝ),
    (5261 / 5376 : ℝ),
    (1229 / 840 : ℝ)]

theorem CurvatureCertificates_lambdaBernsteinLow_pos (i : Fin 9) : 0 < CurvatureCertificates_lambdaBernsteinLow i := by
  fin_cases i <;> norm_num [CurvatureCertificates_lambdaBernsteinLow]

theorem CurvatureCertificates_lambdaBernsteinHigh_pos (i : Fin 9) : 0 < CurvatureCertificates_lambdaBernsteinHigh i := by
  fin_cases i <;> norm_num [CurvatureCertificates_lambdaBernsteinHigh]

end LeanBlast.CourtadeKumar
end
end

end OAI
